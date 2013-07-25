--
-- (c) The University of Glasgow
--

module Avail (
    Avails,
    AvailInfo(..),
    availsToNameSet,
    availsToNameEnv,
    availName, availNames, availFlds, availRecSel, availOverloadedRecSel,
    stableAvailCmp,
    gresFromAvails,
    gresFromAvail
  ) where

import Name
import NameEnv
import NameSet
import RdrName
import OccName

import Binary
import Outputable
import Util

import Data.Foldable (foldMap)
import Data.List
import Data.Maybe

-- -----------------------------------------------------------------------------
-- The AvailInfo type

-- | Records what things are "available", i.e. in scope
data AvailInfo = Avail Name      -- ^ An ordinary identifier in scope
               | AvailTC Name
                         [Name]
                         [OccName]
                                 -- ^ A type or class in scope. Parameters:
                                 --
                                 --  1) The name of the type or class
                                 --  2) The available pieces of type or class.
                                 --  3) The record fields of the type.
                                 --
                                 -- The AvailTC Invariant:
                                 --   * If the type or class is itself
                                 --     to be in scope, it must be
                                 --     *first* in this list.  Thus,
                                 --     typically: @AvailTC Eq [Eq, ==, \/=]@
                                 --   * For every field, the corresponding
                                 --     selector must also be available.
                deriving( Eq )
                        -- Equality used when deciding if the
                        -- interface has changed

-- | A collection of 'AvailInfo' - several things that are \"available\"
type Avails = [AvailInfo]

-- | Compare lexicographically
stableAvailCmp :: AvailInfo -> AvailInfo -> Ordering
stableAvailCmp (Avail n1)         (Avail n2)     = n1 `stableNameCmp` n2
stableAvailCmp (Avail {})         (AvailTC {})   = LT
stableAvailCmp (AvailTC n ns nfs) (AvailTC m ms mfs) =
    (n `stableNameCmp` m) `thenCmp`
    (cmpList stableNameCmp ns ms) `thenCmp`
    (cmpList compare nfs mfs)
stableAvailCmp (AvailTC {})       (Avail {})     = GT


-- -----------------------------------------------------------------------------
-- Operations on AvailInfo

availsToNameSet :: [AvailInfo] -> NameSet
availsToNameSet avails = foldr add emptyNameSet avails
      where add avail set = addListToNameSet set (availNames avail)

availsToNameEnv :: [AvailInfo] -> NameEnv AvailInfo
availsToNameEnv avails = foldr add emptyNameEnv avails
     where add avail env = extendNameEnvList env
                                (zip (availNames avail) (repeat avail))

-- | Just the main name made available, i.e. not the available pieces
-- of type or class brought into scope by the 'GenAvailInfo'
availName :: AvailInfo -> Name
availName (Avail n)       = n
availName (AvailTC n _ _) = n

-- | All names made available by the availability information
availNames :: AvailInfo -> [Name]
availNames (Avail n)        = [n]
availNames (AvailTC _ ns _) = ns

-- | Fields made available by the availability information
availFlds :: AvailInfo -> [OccName]
availFlds (AvailTC _ _ fs) = fs
availFlds _                = []

-- | Find the name of the record selector for a field label
availRecSel :: AvailInfo -> OccName -> Maybe Name
availRecSel (AvailTC p ns _) lbl = find it ns
  where
    it n    = (nameOccName n == sel_occ) || (nameOccName n == lbl)
    sel_occ = mkRecSelOcc lbl (nameOccName p) 
availRecSel _ _ = Nothing

-- | Find the name of the overloaded record selector for a field label
availOverloadedRecSel :: AvailInfo -> OccName -> Maybe Name
availOverloadedRecSel (AvailTC p ns _) lbl = find it ns
  where
    it n    = nameOccName n == sel_occ
    sel_occ = mkRecSelOcc lbl (nameOccName p) 
availOverloadedRecSel _ _ = Nothing

-- | List the (field label, selector) pairs for any overloaded fields
availOverloadedFlds :: AvailInfo -> [(OccName, Name)]
availOverloadedFlds a = foldMap overloaded (availFlds a)
  where
    overloaded fld = case availOverloadedRecSel a fld of
        Just name -> [(fld, name)]
        _         -> []

-- | make a 'GlobalRdrEnv' where all the elements point to the same
-- Provenance (useful for "hiding" imports, or imports with
-- no details).
gresFromAvails :: Provenance -> [AvailInfo] -> [GlobalRdrElt]
gresFromAvails prov avails
  = concatMap (gresFromAvail (const prov) (const prov)) avails

gresFromAvail :: (Name -> Provenance) -> ((OccName, Name) -> Provenance) ->
                     AvailInfo -> [GlobalRdrElt]
gresFromAvail prov_fn prov_fld avail
  = [ GRE {gre_name = sel_name,
           gre_par = fldParent fld avail,
           gre_prov = prov_fld (fld, sel_name)}
    | (fld, sel_name) <- availOverloadedFlds avail ]
    ++
    [ GRE {gre_name = n,
           gre_par = parent n avail,
           gre_prov = prov_fn n}
    | n <- availNames avail ]
  where
    parent _ (Avail _)                   = NoParent
    parent n (AvailTC m _ _) | n == m    = NoParent
                             | otherwise = ParentIs m

    fldParent fld (AvailTC p _ _) = FldParent p fld
    fldParent _   _               = panic "gresFromAvail/fldParent"

-- -----------------------------------------------------------------------------
-- Printing

instance Outputable AvailInfo where
   ppr = pprAvail

pprAvail :: AvailInfo -> SDoc
pprAvail (Avail n)          = ppr n
pprAvail (AvailTC n ns nfs) = ppr n <> braces (hsep (punctuate comma (map ppr ns ++ map ppr nfs)))

instance Binary AvailInfo where
    put_ bh (Avail aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (AvailTC ab ac ad) = do
            putByte bh 1
            put_ bh ab
            put_ bh ac
            put_ bh ad
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (Avail aa)
              _ -> do ab <- get bh
                      ac <- get bh
                      ad <- get bh
                      return (AvailTC ab ac ad)

