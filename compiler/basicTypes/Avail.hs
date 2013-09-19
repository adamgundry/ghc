--
-- (c) The University of Glasgow
--

{-# LANGUAGE DeriveDataTypeable #-}

module Avail (
    Avails, AvailFlds(..), AvailFields, FieldLabelString,
    AvailInfo(..),
    availsToNameSet,
    availsToNameSetWithSelectors,
    availsToNameEnv,
    availName, availNames, availNonFldNames,
    availNamesWithSelectors,
    availFlds, availOverloadedFlds,
    stableAvailCmp, stableAvailFieldsCmp,
    nullAvailFields,
    availFieldsLabels,
    availFieldsNames,
    isOverloaded,
    fieldLabelsToAvailFields,
    fieldLabelsToAvailFields',
    gresFromAvails,
    gresFromAvail,
    pprAvailFields
  ) where

import Name
import NameEnv
import NameSet
import RdrName

import FieldLabel
import Binary
import Outputable
import Util

import Data.Function
import Data.Data

-- -----------------------------------------------------------------------------
-- The AvailInfo type

-- | Records what things are "available", i.e. in scope
data AvailInfo = Avail Name      -- ^ An ordinary identifier in scope
               | AvailTC Name
                         [Name]
                         AvailFields
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
                deriving( Eq )
                        -- Equality used when deciding if the
                        -- interface has changed

-- | A collection of 'AvailInfo' - several things that are \"available\"
type Avails = [AvailInfo]

-- | Record fields in an 'AvailInfo'
-- See Note [Representing fields in AvailInfo]
data AvailFlds name = NonOverloaded [name] | Overloaded [(FieldLabelString, name)]
  deriving (Eq, Data, Typeable)

type AvailFields = AvailFlds Name

{-
Note [Representing fields in AvailInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When -XOverloadedRecordFields is disabled (the normal case), a
datatype like

  data T = MkT { foo :: Int }

gives rise to the AvailInfo

  AvailTC T [T, MkT] (NonOverloaded [foo]),

whereas if -XOverloadedRecordFields is enabled it gives

  AvailTC T [T, MkT] (Overloaded [(foo, $sel:foo:T)])

since the label does not match the selector name.

The labels in an Overloaded field list are not necessarily unique:
data families allow the same parent (the family tycon) to have
multiple distinct fields with the same label. For example,

  data family F a
  data instance F Int  = MkFInt { foo :: Int }
  data instance F Bool = MkFBool { foo :: Bool}

gives rise to

  AvailTC F [F, MkFInt, MkFBool]
    (Overloaded [(foo, $sel:foo:R:FInt), (foo, $sel:foo:R:FBool)]).
-}

fieldLabelsToAvailFields :: [FieldLabel] -> AvailFields
fieldLabelsToAvailFields [] = NonOverloaded []
fieldLabelsToAvailFields fls@(fl:_) = fieldLabelsToAvailFields' overloaded fls
  where overloaded = isOverloadedFieldLabel fl

fieldLabelsToAvailFields' :: Bool -> [FieldLabel] -> AvailFields
fieldLabelsToAvailFields' overloaded fls
    | overloaded = Overloaded (map (\ fl -> (flLabel fl, flSelector fl)) fls)
    | otherwise  = NonOverloaded (map flSelector fls)


-- | Compare lexicographically
stableAvailCmp :: AvailInfo -> AvailInfo -> Ordering
stableAvailCmp (Avail n1)         (Avail n2)     = n1 `stableNameCmp` n2
stableAvailCmp (Avail {})         (AvailTC {})   = LT
stableAvailCmp (AvailTC n ns nfs) (AvailTC m ms mfs) =
    (n `stableNameCmp` m) `thenCmp`
    (cmpList stableNameCmp ns ms) `thenCmp`
    (stableAvailFieldsCmp nfs mfs)
stableAvailCmp (AvailTC {})       (Avail {})     = GT

stableAvailFieldsCmp :: AvailFields -> AvailFields -> Ordering
stableAvailFieldsCmp (NonOverloaded xs) (NonOverloaded ys) = cmpList stableNameCmp xs ys
stableAvailFieldsCmp (NonOverloaded {}) (Overloaded {})    = LT
stableAvailFieldsCmp (Overloaded xs)    (Overloaded ys)    = cmpList (stableNameCmp `on` snd) xs ys
stableAvailFieldsCmp (Overloaded {})    (NonOverloaded {}) = GT

-- -----------------------------------------------------------------------------
-- Operations on AvailInfo

availsToNameSet :: [AvailInfo] -> NameSet
availsToNameSet avails = foldr add emptyNameSet avails
      where add avail set = addListToNameSet set (availNames avail)

availsToNameSetWithSelectors :: [AvailInfo] -> NameSet
availsToNameSetWithSelectors avails = foldr add emptyNameSet avails
      where add avail set = addListToNameSet set (availNamesWithSelectors avail)

availsToNameEnv :: [AvailInfo] -> NameEnv AvailInfo
availsToNameEnv avails = foldr add emptyNameEnv avails
     where add avail env = extendNameEnvList env
                                (zip (availNames avail) (repeat avail))

-- | Just the main name made available, i.e. not the available pieces
-- of type or class brought into scope by the 'GenAvailInfo'
availName :: AvailInfo -> Name
availName (Avail n)       = n
availName (AvailTC n _ _) = n

-- | All names made available by the availability information (excluding selectors)
availNames :: AvailInfo -> [Name]
availNames (Avail n)                         = [n]
availNames (AvailTC _ ns (NonOverloaded fs)) = ns ++ fs
availNames (AvailTC _ ns (Overloaded _))     = ns

-- | All names made available by the availability information (including selectors)
availNamesWithSelectors :: AvailInfo -> [Name]
availNamesWithSelectors (Avail n)         = [n]
availNamesWithSelectors (AvailTC _ ns fs) = ns ++ availFieldsNames fs

-- | Names for non-fields made available by the availability information
availNonFldNames :: AvailInfo -> [Name]
availNonFldNames (Avail n)        = [n]
availNonFldNames (AvailTC _ ns _) = ns

-- | Fields made available by the availability information
availFlds :: AvailInfo -> AvailFields
availFlds (AvailTC _ _ fs) = fs
availFlds _                = NonOverloaded []

-- | Fields made available by the availability information
availOverloadedFlds :: AvailInfo -> [(FieldLabelString, Name)]
availOverloadedFlds (AvailTC _ _ (Overloaded fs)) = fs
availOverloadedFlds _                             = []

-- -----------------------------------------------------------------------------
-- Operations on AvailFields

nullAvailFields :: AvailFields -> Bool
nullAvailFields (NonOverloaded xs) = null xs
nullAvailFields (Overloaded xs)    = null xs

availFieldsLabels :: AvailFields -> [FieldLabelString]
availFieldsLabels (NonOverloaded xs) = map (occNameFS . nameOccName) xs
availFieldsLabels (Overloaded xs)    = map fst xs

availFieldsNames :: AvailFlds name -> [name]
availFieldsNames (NonOverloaded xs) = xs
availFieldsNames (Overloaded xs)    = map snd xs

isOverloaded :: AvailFields -> Bool
isOverloaded (NonOverloaded _) = False
isOverloaded (Overloaded _)    = True

-- -----------------------------------------------------------------------------
-- gresFromAvails

-- | make a 'GlobalRdrEnv' where all the elements point to the same
-- Provenance (useful for "hiding" imports, or imports with
-- no details).
gresFromAvails :: Provenance -> [AvailInfo] -> [GlobalRdrElt]
gresFromAvails prov avails
  = concatMap (gresFromAvail (const prov) (const prov)) avails

gresFromAvail :: (Name -> Provenance) -> (FieldLabelString -> Provenance) ->
                     AvailInfo -> [GlobalRdrElt]
gresFromAvail prov_fn prov_fld avail = xs ++ ys
  where
    parent _ (Avail _)                   = NoParent
    parent n (AvailTC m _ _) | n == m    = NoParent
                             | otherwise = ParentIs m

    xs = case availFlds avail of
           NonOverloaded ns -> map greFromNonOverloadedFld ns
           Overloaded fs    -> map greFromOverloadedFld fs
    ys = map greFromNonFld (availNonFldNames avail)

    greFromNonFld n = GRE { gre_name = n, gre_par = parent n avail, gre_prov = prov_fn n}

    greFromNonOverloadedFld n
      = GRE { gre_name = n
            , gre_par  = FldParent (availName avail) (occNameFS (nameOccName n))
            , gre_prov = prov_fld (occNameFS (nameOccName n)) }

    greFromOverloadedFld (lbl, sel)
      = GRE { gre_name = sel
            , gre_par  = FldParent (availName avail) lbl
            , gre_prov = prov_fld lbl }

-- -----------------------------------------------------------------------------
-- Printing

instance Outputable AvailInfo where
   ppr = pprAvail

pprAvail :: AvailInfo -> SDoc
pprAvail (Avail n)          = ppr n
pprAvail (AvailTC n ns nfs) = ppr n <> braces (hsep (punctuate comma (map ppr ns ++ pprAvailFields nfs)))

instance Outputable n => Outputable (AvailFlds n) where
    ppr flds = braces $ hsep $ punctuate comma $ pprAvailFields flds

pprAvailFields :: Outputable n => AvailFlds n -> [SDoc]
pprAvailFields (Overloaded xs)    = map ppr xs
pprAvailFields (NonOverloaded xs) = map ppr xs

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

instance Binary n => Binary (AvailFlds n) where
    put_ bh (NonOverloaded xs) = do
        putByte bh 0
        put_ bh xs
    put_ bh (Overloaded xs) = do
        putByte bh 1
        put_ bh xs
    get bh = do
        h <- getByte bh
        case h of
            0 -> do xs <- get bh
                    return (NonOverloaded xs)
            _ -> do xs <- get bh
                    return (Overloaded xs)
