--
-- (c) The University of Glasgow
--

module Avail (
    Avails,
    AvailInfo(..),
    availsToNameSet,
    availsToNameEnv,
    availName, availNames, availNonFldNames, availFlds,
    stableAvailCmp, stableFieldLabelCmp,
    gresFromAvails,
    gresFromAvail
  ) where

import Name
import NameEnv
import NameSet
import RdrName
import OccName
import TyCon

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
                         [FieldLabel]
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

-- | Compare lexicographically
stableAvailCmp :: AvailInfo -> AvailInfo -> Ordering
stableAvailCmp (Avail n1)         (Avail n2)     = n1 `stableNameCmp` n2
stableAvailCmp (Avail {})         (AvailTC {})   = LT
stableAvailCmp (AvailTC n ns nfs) (AvailTC m ms mfs) =
    (n `stableNameCmp` m) `thenCmp`
    (cmpList stableNameCmp ns ms) `thenCmp`
    (cmpList stableFieldLabelCmp nfs mfs)
stableAvailCmp (AvailTC {})       (Avail {})     = GT

stableFieldLabelCmp :: FieldLabel -> FieldLabel -> Ordering
stableFieldLabelCmp (FieldLabel occ sel _) (FieldLabel occ' sel' _)
    = compare occ occ' `thenCmp` stableNameCmp sel sel'


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
availNames (Avail n)         = [n]
availNames (AvailTC _ ns fs) = ns ++ map flSelector fs

-- | Names for non-fields made available by the availability information
availNonFldNames :: AvailInfo -> [Name]
availNonFldNames (Avail n)        = [n]
availNonFldNames (AvailTC _ ns _) = ns

-- | Fields made available by the availability information
availFlds :: AvailInfo -> [FieldLabel]
availFlds (AvailTC _ _ fs) = fs
availFlds _                = []

-- | make a 'GlobalRdrEnv' where all the elements point to the same
-- Provenance (useful for "hiding" imports, or imports with
-- no details).
gresFromAvails :: Provenance -> [AvailInfo] -> [GlobalRdrElt]
gresFromAvails prov avails
  = concatMap (gresFromAvail (const prov) (const prov)) avails

gresFromAvail :: (Name -> Provenance) -> (FieldLabel -> Provenance) ->
                     AvailInfo -> [GlobalRdrElt]
gresFromAvail prov_fn prov_fld avail
  = [ GRE {gre_name = flSelector fl,
           gre_par = fldParent fl avail,
           gre_prov = prov_fld fl}
    | fl <- availFlds avail ]
    ++
    [ GRE {gre_name = n,
           gre_par = parent n avail,
           gre_prov = prov_fn n}
    | n <- availNonFldNames avail ]
  where
    parent _ (Avail _)                                 = NoParent
    parent n (AvailTC m _ _) | n == m                  = NoParent
                             | otherwise               = ParentIs m

    fldParent fl (AvailTC p _ _)  = FldParent p (flOccName fl) (flInstances fl)
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

