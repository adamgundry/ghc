The @FamInst@ type: family instance heads

\begin{code}
{-# LANGUAGE GADTs #-}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module FamInst ( 
        checkFamInstConsistency, tcExtendLocalFamInstEnv,
        tcLookupFamInst, lookupRecFldInsts,
        tcGetFamInstEnvs,
        newFamInst,
        TcBuiltInSynFamily(..), trivialBuiltInFamily
    ) where

import Pair(Pair)
import HscTypes
import FamInstEnv
import InstEnv( roughMatchTcs )
import Coercion( pprCoAxBranchHdr )
import LoadIface
import Type
import TypeRep
import TcRnMonad
import Unify
import TyCon
import DataCon
import CoAxiom
import DynFlags
import Module
import Outputable
import UniqFM
import FastString
import Util
import Maybes
import TcMType
import TcType
import TcEnv
import Id
import Name
import NameEnv
import RdrName
import RnEnv
import Var
import VarSet
import PrelNames
import ErrUtils
import Control.Monad
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import TcEvidence(TcCoercion)

#include "HsVersions.h"
\end{code}

%************************************************************************
%*									*
                 Making a FamInst
%*									*
%************************************************************************

\begin{code}
-- All type variables in a FamInst must be fresh. This function
-- creates the fresh variables and applies the necessary substitution
-- It is defined here to avoid a dependency from FamInstEnv on the monad
-- code.

newFamInst :: FamFlavor -> CoAxiom Unbranched -> TcRnIf gbl lcl FamInst
-- Freshen the type variables of the FamInst branches
-- Called from the vectoriser monad too, hence the rather general type
newFamInst flavor axiom@(CoAxiom { co_ax_branches = FirstBranch branch
                                 , co_ax_tc = fam_tc })
  = do { (subst, tvs') <- tcInstSkolTyVarsLoc loc tvs
       ; return (FamInst { fi_fam      = fam_tc_name
                         , fi_flavor   = flavor
                         , fi_tcs      = roughMatchTcs lhs
                         , fi_tvs      = tvs'
                         , fi_tys      = substTys subst lhs
                         , fi_rhs      = substTy  subst rhs
                         , fi_axiom    = axiom }) }
  where
    fam_tc_name = tyConName fam_tc
    CoAxBranch { cab_loc = loc
               , cab_tvs = tvs
               , cab_lhs = lhs
               , cab_rhs = rhs } = branch

\end{code}


%************************************************************************
%*									*
	Optimised overlap checking for family instances
%*									*
%************************************************************************

For any two family instance modules that we import directly or indirectly, we
check whether the instances in the two modules are consistent, *unless* we can
be certain that the instances of the two modules have already been checked for
consistency during the compilation of modules that we import.

Why do we need to check?  Consider 
   module X1 where	  	  module X2 where
    data T1			    data T2
    type instance F T1 b = Int	    type instance F a T2 = Char
    f1 :: F T1 a -> Int		    f2 :: Char -> F a T2
    f1 x = x			    f2 x = x

Now if we import both X1 and X2 we could make (f2 . f1) :: Int -> Char.
Notice that neither instance is an orphan.

How do we know which pairs of modules have already been checked?  Any pair of
modules where both modules occur in the `HscTypes.dep_finsts' set (of the
`HscTypes.Dependencies') of one of our directly imported modules must have
already been checked.  Everything else, we check now.  (So that we can be
certain that the modules in our `HscTypes.dep_finsts' are consistent.)

\begin{code}
-- The optimisation of overlap tests is based on determining pairs of modules
-- whose family instances need to be checked for consistency.
--
data ModulePair = ModulePair Module Module

-- canonical order of the components of a module pair
--
canon :: ModulePair -> (Module, Module)
canon (ModulePair m1 m2) | m1 < m2   = (m1, m2)
			 | otherwise = (m2, m1)

instance Eq ModulePair where
  mp1 == mp2 = canon mp1 == canon mp2

instance Ord ModulePair where
  mp1 `compare` mp2 = canon mp1 `compare` canon mp2

instance Outputable ModulePair where
  ppr (ModulePair m1 m2) = angleBrackets (ppr m1 <> comma <+> ppr m2)

-- Sets of module pairs
--
type ModulePairSet = Map ModulePair ()

listToSet :: [ModulePair] -> ModulePairSet
listToSet l = Map.fromList (zip l (repeat ()))

checkFamInstConsistency :: [Module] -> [Module] -> TcM ()
checkFamInstConsistency famInstMods directlyImpMods
  = do { dflags     <- getDynFlags
       ; (eps, hpt) <- getEpsAndHpt

       ; let { -- Fetch the iface of a given module.  Must succeed as
 	       -- all directly imported modules must already have been loaded.
	       modIface mod = 
	         case lookupIfaceByModule dflags hpt (eps_PIT eps) mod of
                   Nothing    -> panic "FamInst.checkFamInstConsistency"
                   Just iface -> iface

             ; hmiModule     = mi_module . hm_iface
	     ; hmiFamInstEnv = extendFamInstEnvList emptyFamInstEnv 
                               . md_fam_insts . hm_details
             ; hpt_fam_insts = mkModuleEnv [ (hmiModule hmi, hmiFamInstEnv hmi) 
			                   | hmi <- eltsUFM hpt]
	     ; groups        = map (dep_finsts . mi_deps . modIface) 
				   directlyImpMods
	     ; okPairs       = listToSet $ concatMap allPairs groups
	         -- instances of okPairs are consistent
	     ; criticalPairs = listToSet $ allPairs famInstMods
	         -- all pairs that we need to consider
             ; toCheckPairs  = Map.keys $ criticalPairs `Map.difference` okPairs
	         -- the difference gives us the pairs we need to check now
	     }

       ; mapM_ (check hpt_fam_insts) toCheckPairs
       }
  where
    allPairs []     = []
    allPairs (m:ms) = map (ModulePair m) ms ++ allPairs ms

    check hpt_fam_insts (ModulePair m1 m2)
      = do { env1 <- getFamInsts hpt_fam_insts m1
           ; env2 <- getFamInsts hpt_fam_insts m2
           ; mapM_ (checkForConflicts (emptyFamInstEnv, env2))   
                   (famInstEnvElts env1) }

getFamInsts :: ModuleEnv FamInstEnv -> Module -> TcM FamInstEnv
getFamInsts hpt_fam_insts mod
  | Just env <- lookupModuleEnv hpt_fam_insts mod = return env
  | otherwise = do { _ <- initIfaceTcRn (loadSysInterface doc mod)
                   ; eps <- getEps
                   ; return (expectJust "checkFamInstConsistency" $
                             lookupModuleEnv (eps_mod_fam_inst_env eps) mod) }
  where
    doc = ppr mod <+> ptext (sLit "is a family-instance module")
\end{code}

%************************************************************************
%*									*
	Lookup
%*									*
%************************************************************************

Look up the instance tycon of a family instance.

The match may be ambiguous (as we know that overlapping instances have
identical right-hand sides under overlapping substitutions - see
'FamInstEnv.lookupFamInstEnvConflicts').  However, the type arguments used
for matching must be equal to or be more specific than those of the family
instance declaration.  We pick one of the matches in case of ambiguity; as
the right-hand sides are identical under the match substitution, the choice
does not matter.

Return the instance tycon and its type instance.  For example, if we have

 tcLookupFamInst 'T' '[Int]' yields (':R42T', 'Int')

then we have a coercion (ie, type instance of family instance coercion)

 :Co:R42T Int :: T [Int] ~ :R42T Int

which implies that :R42T was declared as 'data instance T [a]'.

\begin{code}
tcLookupFamInst :: TyCon -> [Type] -> TcM (Maybe FamInstMatch)
tcLookupFamInst tycon tys
  | not (isOpenFamilyTyCon tycon)
  = return Nothing

tcLookupFamInst fam tys@(r:f:_)
  | isRecordsFam fam
  , Just lbl     <- isStrLitTy f
  , Just (tc, args) <- tcSplitTyConApp_maybe r
  = lookupRecFldFamInst fam lbl tc args tys

tcLookupFamInst tycon tys
  = do { instEnv <- tcGetFamInstEnvs
       ; let mb_match = lookupFamInstEnv instEnv tycon tys 
       ; traceTc "lookupFamInst" ((ppr tycon <+> ppr tys) $$ 
                                  pprTvBndrs (varSetElems (tyVarsOfTypes tys)) $$ 
                                  ppr mb_match $$ ppr instEnv)
       ; case mb_match of
	   [] -> return Nothing
	   (match:_) 
              -> return $ Just match
       }
\end{code}


%************************************************************************
%*									*
	Lookup record field instances
%*									*
%************************************************************************

The GetResult and SetResult type families (defined in GHC.Records) are
magical, in that rather than looking for instances in the usual way,
we use lookupRecFldFamInst defined below. This delegates most of the
work to lookupRecFldInsts, which is also used when looking for
instances of the Has and Upd classes (by matchClassInst in
TcInteract).

The idea is that when we are looking for a family instance matching

    GetResult (T a b c) "foo"

we check if field foo belonging to type T is in scope, and if so,
create a suitable match from the axiom created by
makeOverloadedRecFldInsts in TcInstDcls (see Note [Instance scoping
for OverloadedRecordFields] in TcInstDcls). The picture is slightly
complicated when T is a data family, because then the field actually
belongs to the representation tycon, though T is its parent for
lexical scope purposes.

Note [Duplicate field labels with data families]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following example:

    module M where
      data family F a
      data instance F Int = MkF1 { foo :: Int }

    module N where
      import M
      data instance F Char = MkF2 { foo :: Char }

Both fields have the same lexical parent (the family tycon F)!  Thus
it is not enough to lookup the field in the GlobalRdrEnv with
lookupSubBndrGREs: we also need to check the selector names to find
the one with the right representation tycon.

\begin{code}
lookupRecFldFamInst :: TyCon -> FastString -> TyCon -> [Type] -> [Type] -> TcM (Maybe FamInstMatch)
lookupRecFldFamInst fam lbl tc args tys
  = do { mb_insts <- lookupRecFldInsts lbl tc args
       ; mb_fam_inst <- case mb_insts of
           Nothing          -> return Nothing
           Just (Left  xs)  -> return $ Just (get_or_set xs)
           Just (Right fis) -> fmap (fmap (fam_inst_for . toUnbranchedAxiom) . snd) $
                                   tryTc $ tcLookupAxiom (get_or_set_fis fis)
       ; return $ do { fam_inst <- mb_fam_inst
                     ; subst <- tcMatchTys (mkVarSet (fi_tvs fam_inst)) (fi_tys fam_inst) tys
                     ; return $ FamInstMatch fam_inst (substTyVars subst (fi_tvs fam_inst)) } }
  where
    is_get = isGetResultFam fam
    get_or_set (_, _, get, set) | is_get    = get
                                | otherwise = set
    get_or_set_fis | is_get    = fldInstsGetResult
                   | otherwise = fldInstsSetResult

    fam_inst_for axiom | is_get    = mkImportedFamInst getResultFamName
                                         [Just (tyConName tc), Nothing] axiom
                       | otherwise = mkImportedFamInst setResultFamName
                                         [Just (tyConName tc), Nothing, Nothing] axiom

lookupRecFldInsts :: FastString -> TyCon -> [Type]
                         -> TcM (Maybe (Either (DFunId, DFunId, FamInst, FamInst) (FldInsts Name)))
lookupRecFldInsts lbl tc args
  = do { rep_tc <- if isDataFamilyTyCon tc
                   then do { mb_fi <- tcLookupFamInst tc args
                           ; return $ case mb_fi of
                               Nothing  -> tc
                               Just fim -> tcTyConAppTyCon (fi_rhs (fim_instance fim)) }
                   else return tc
       ; case find ((== lbl_occ) . flOccName) (tyConFieldLabels rep_tc) of
           Nothing -> return Nothing -- This field doesn't belong to the datatype!
           Just fl -> do
               { gbl_env <- getGblEnv
               ; let rep_tc_occ = getOccName rep_tc
                     mod        = nameModule (tyConName rep_tc)
                     sel_name   = flSelector fl
                     gres       = lookupSubBndrGREs (tcg_rdr_env gbl_env) parent lbl_rdr
                 -- See Note [Duplicate field labels with data families]
               ; if any ((sel_name ==) . gre_name) gres
                 then case lookupNameEnv (tcg_fld_inst_env gbl_env) sel_name of
                        Just xs -> return $ Just (Left xs)
                        Nothing -> fmap (Just . Right) $
                                       lookupRecFldInstNames mod lbl_occ rep_tc_occ
                 else return Nothing } }
  where
    parent  = ParentIs (tyConName tc)
    lbl_occ = mkVarOccFS lbl
    lbl_rdr = mkRdrUnqual lbl_occ
\end{code}



%************************************************************************
%*									*
	Extending the family instance environment
%*									*
%************************************************************************

\begin{code}
-- Add new locally-defined family instances
tcExtendLocalFamInstEnv :: [FamInst] -> TcM a -> TcM a
tcExtendLocalFamInstEnv fam_insts thing_inside
 = do { env <- getGblEnv
      ; (inst_env', fam_insts') <- foldlM addLocalFamInst  
                                          (tcg_fam_inst_env env, tcg_fam_insts env)
                                          fam_insts
      ; let env' = env { tcg_fam_insts    = fam_insts'
		       , tcg_fam_inst_env = inst_env' }
      ; setGblEnv env' thing_inside 
      }

-- Check that the proposed new instance is OK, 
-- and then add it to the home inst env
-- This must be lazy in the fam_inst arguments, see Note [Lazy axiom match]
-- in FamInstEnv.lhs
addLocalFamInst :: (FamInstEnv,[FamInst]) -> FamInst -> TcM (FamInstEnv, [FamInst])
addLocalFamInst (home_fie, my_fis) fam_inst
        -- home_fie includes home package and this module
        -- my_fies is just the ones from this module
  = do { traceTc "addLocalFamInst" (ppr fam_inst)

       ; isGHCi <- getIsGHCi
 
           -- In GHCi, we *override* any identical instances
           -- that are also defined in the interactive context
       ; let (home_fie', my_fis') 
               | isGHCi    = ( deleteFromFamInstEnv home_fie fam_inst
                             , filterOut (identicalFamInst fam_inst) my_fis)
               | otherwise = (home_fie, my_fis)

           -- Load imported instances, so that we report
           -- overlaps correctly
       ; eps <- getEps
       ; let inst_envs  = (eps_fam_inst_env eps, home_fie')
             home_fie'' = extendFamInstEnv home_fie fam_inst

           -- Check for conflicting instance decls
       ; no_conflict <- checkForConflicts inst_envs fam_inst
       ; if no_conflict then
            return (home_fie'', fam_inst : my_fis')
         else 
            return (home_fie,   my_fis) }

\end{code}

%************************************************************************
%*									*
	Checking an instance against conflicts with an instance env
%*									*
%************************************************************************

Check whether a single family instance conflicts with those in two instance
environments (one for the EPS and one for the HPT).

\begin{code}
checkForConflicts :: FamInstEnvs -> FamInst -> TcM Bool
checkForConflicts inst_envs fam_inst
  = do { let conflicts = lookupFamInstEnvConflicts inst_envs fam_inst
             no_conflicts = null conflicts
       ; traceTc "checkForConflicts" (ppr (map fim_instance conflicts) $$
                                      ppr fam_inst $$ ppr inst_envs)
       ; unless no_conflicts $ conflictInstErr fam_inst conflicts
       ; return no_conflicts }

conflictInstErr :: FamInst -> [FamInstMatch] -> TcRn ()
conflictInstErr fam_inst conflictingMatch
  | (FamInstMatch { fim_instance = confInst }) : _ <- conflictingMatch
  = addFamInstsErr (ptext (sLit "Conflicting family instance declarations:"))
                   [fam_inst, confInst]
  | otherwise 
  = panic "conflictInstErr"

addFamInstsErr :: SDoc -> [FamInst] -> TcRn ()
addFamInstsErr herald insts
  = ASSERT( not (null insts) )
    setSrcSpan srcSpan $ addErr $
    hang herald
       2 (vcat [ pprCoAxBranchHdr (famInstAxiom fi) 0
               | fi <- sorted ])
 where
   getSpan   = getSrcLoc . famInstAxiom
   sorted    = sortWith getSpan insts
   fi1       = head sorted
   srcSpan   = coAxBranchSpan (coAxiomSingleBranch (famInstAxiom fi1))
   -- The sortWith just arranges that instances are dislayed in order
   -- of source location, which reduced wobbling in error messages,
   -- and is better for users

tcGetFamInstEnvs :: TcM FamInstEnvs
-- Gets both the external-package inst-env
-- and the home-pkg inst env (includes module being compiled)
tcGetFamInstEnvs 
  = do { eps <- getEps; env <- getGblEnv
       ; return (eps_fam_inst_env eps, tcg_fam_inst_env env) }
\end{code}


Type checking of built-in families
==================================

\begin{code}
data TcBuiltInSynFamily = TcBuiltInSynFamily
  { sfMatchFam      :: [Type] -> Maybe (TcCoercion, TcType)
  , sfInteractTop   :: [Type] -> Type -> [Pair TcType]
  , sfInteractInert :: [Type] -> Type ->
                       [Type] -> Type -> [Pair TcType]
  }

-- Provides default implementations that do nothing.
trivialBuiltInFamily :: TcBuiltInSynFamily
trivialBuiltInFamily = TcBuiltInSynFamily
  { sfMatchFam      = \_ -> Nothing
  , sfInteractTop   = \_ _ -> []
  , sfInteractInert = \_ _ _ _ -> []
  }
\end{code}


