--
-- (c) The University of Glasgow
--

{-# LANGUAGE DeriveDataTypeable #-}

module Avail (
    Avails, AvailFlds(..), AvailFields,
    AvailInfo(..),
    availsToNameSet,
    availsToNameSetWithSelectors,
    availsToNameEnv,
    availName, availNames, availNonFldNames,
    availFlds, availOverloadedFlds,
    stableAvailCmp, stableAvailFieldsCmp,
    nullAvailFields,
    availFieldsOccs,
    availFieldsNames,
    isOverloaded,
    pprAvailFields
  ) where

import Name
import NameEnv
import NameSet

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
data AvailFlds name = NonOverloaded [name] | Overloaded [(OccName, name)]
  deriving (Eq, Data, Typeable)

type AvailFields = AvailFlds Name


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
availOverloadedFlds :: AvailInfo -> [(OccName, Name)]
availOverloadedFlds (AvailTC _ _ (Overloaded fs)) = fs
availOverloadedFlds _                             = []

-- -----------------------------------------------------------------------------
-- Operations on AvailFields

nullAvailFields :: AvailFields -> Bool
nullAvailFields (NonOverloaded xs) = null xs
nullAvailFields (Overloaded xs)    = null xs

availFieldsOccs :: AvailFields -> [OccName]
availFieldsOccs (NonOverloaded xs) = map nameOccName xs
availFieldsOccs (Overloaded xs)    = map fst xs

availFieldsNames :: AvailFlds name -> [name]
availFieldsNames (NonOverloaded xs) = xs
availFieldsNames (Overloaded xs)    = map snd xs

isOverloaded :: AvailFields -> Bool
isOverloaded (NonOverloaded _) = False
isOverloaded (Overloaded _)    = True

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
