%
% (c) Adam Gundry 2013
%

\begin{code}

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module FieldLabel ( FieldLabelString
                  , FieldLabelEnv
                  , FieldLbl(..)
                  , FieldLabel
                  , mkFieldLabelOccs
                  ) where

import OccName
import Name

import Binary
import FastString
import FastStringEnv
import Outputable

import Data.Foldable
import Data.Traversable

-- | Field labels are just represented as strings;
-- they are not necessarily unique (even within a module)
type FieldLabelString = FastString

-- | A map from labels to all the auxiliary information
type FieldLabelEnv = FastStringEnv FieldLabel


type FieldLabel = FieldLbl Name

-- | Fields in an algebraic record type
data FieldLbl a = FieldLabel {
      flLabel          :: FieldLabelString, -- ^ Label of the field
      flIsOverloaded   :: Bool,             -- ^ Is this field overloaded?
      flSelector       :: a,                -- ^ Record selector function
      flHasDFun        :: a,                -- ^ DFun for Has class instance
      flUpdDFun        :: a,                -- ^ DFun for Upd class instance
      flGetResultAxiom :: a,                -- ^ Axiom for GetResult family instance
      flSetResultAxiom :: a                 -- ^ Axiom for SetResult family instance
    }
  deriving (Functor, Foldable, Traversable)

instance Outputable a => Outputable (FieldLbl a) where
    ppr fl = ppr (flLabel fl) <> braces (ppr (flSelector fl))

instance Binary a => Binary (FieldLbl a) where
    put_ bh (FieldLabel aa ab ac ad ae af ag) = do
        put_ bh aa
        put_ bh ab
        put_ bh ac
        put_ bh ad
        put_ bh ae
        put_ bh af
        put_ bh ag

    get bh = do
        aa <- get bh
        ab <- get bh
        ac <- get bh
        ad <- get bh
        ae <- get bh
        af <- get bh
        ag <- get bh
        return (FieldLabel aa ab ac ad ae af ag)
\end{code}


Record selector OccNames are built from the underlying field name and
the name of the type constructor, to support overloaded record fields.

\begin{code}
mkFieldLabelOccs :: FieldLabelString -> OccName -> Bool -> FieldLbl OccName
mkFieldLabelOccs lbl tc is_overloaded
  = FieldLabel lbl is_overloaded sel_occ has_occ upd_occ get_occ set_occ
  where
    str     = ":" ++ unpackFS lbl ++ ":" ++ occNameString tc
    has_str = "Has"
    upd_str = "Upd"
    get_str = "GetResult"
    set_str = "SetResult"

    sel_occ | is_overloaded = mkRecFldSelOcc str
            | otherwise     = mkVarOccFS lbl
    has_occ = mkRecFldDFunOcc (has_str ++ str)
    upd_occ = mkRecFldDFunOcc (upd_str ++ str)
    get_occ = mkRecFldAxiomOcc (get_str ++ str)
    set_occ = mkRecFldAxiomOcc (set_str ++ str)
\end{code}
