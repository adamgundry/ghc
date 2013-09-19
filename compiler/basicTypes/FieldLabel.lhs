%
% (c) Adam Gundry 2013
%

\begin{code}

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module FieldLabel ( FieldLabelString
                  , FieldLabelEnv
                  , FieldLbl(..)
                  , FieldLabel
                  , FldInsts(..)
                  , isOverloadedFieldLabel
                  , mkRecSelOcc
                  , mkOverloadedRecFldOccs
                  ) where

import OccName
import Name

import Binary
import FastString
import FastStringEnv
import Outputable

import Data.Foldable
import Data.Traversable


type FieldLabelString = FastString


type FieldLabelEnv = FastStringEnv FieldLabel
type FieldLabel    = FieldLbl Name

-- | Fields in an algebraic record type
data FieldLbl a = FieldLabel {
      flLabel     :: FieldLabelString, -- ^ Label of the field
      flSelector  :: a,                -- ^ Record selector function
      flInstances :: FldInsts a        -- ^ Instances for overloading
    }
  deriving (Functor, Foldable, Traversable)

instance Outputable a => Outputable (FieldLbl a) where
    ppr (FieldLabel occ sel _) = ppr occ <> braces (ppr sel)

instance Binary a => Binary (FieldLbl a) where
    put_ bh (FieldLabel aa ab ac) = do
        put_ bh aa
        put_ bh ab
        put_ bh ac

    get bh = do
        aa <- get bh
        ab <- get bh
        ac <- get bh
        return (FieldLabel aa ab ac)


isOverloadedFieldLabel :: FieldLabel -> Bool
isOverloadedFieldLabel fl = flLabel fl /= occNameFS (nameOccName (flSelector fl))


-- | Represents names for overloaded record field instances, specifically
--   the dfuns for Has and Upd, and axioms for GetResult and SetResult
data FldInsts a = FldInsts { fldInstsHas :: a
                           , fldInstsUpd :: a
                           , fldInstsGetResult :: a
                           , fldInstsSetResult :: a }
  deriving (Functor, Foldable, Traversable)

instance Outputable a => Outputable (FldInsts a) where
  ppr (FldInsts a b c d) = ppr (a, b, c, d)

instance Binary a => Binary (FldInsts a) where
    put_ bh (FldInsts a b c d) = do
        put_ bh a
        put_ bh b
        put_ bh c
        put_ bh d

    get bh = do
        a <- get bh
        b <- get bh
        c <- get bh
        d <- get bh
        return (FldInsts a b c d)
\end{code}


Record selector OccNames are built from the underlying field name and
the name of the type constructor, to support overloaded record fields.

\begin{code}
mkRecSelOcc :: FieldLabelString -> OccName -> OccName
mkRecSelOcc lbl tc = fst $ mkOverloadedRecFldOccs lbl tc

mkOverloadedRecFldOccs :: FieldLabelString -> OccName -> (OccName, FldInsts OccName)
mkOverloadedRecFldOccs lbl tc = (sel_occ, is)
  where
    str     = ":" ++ unpackFS lbl ++ ":" ++ occNameString tc
    has_str = "Has"
    upd_str = "Upd"
    get_str = "GetResult"
    set_str = "SetResult"

    sel_occ = mkRecFldSelOcc str
    has_occ = mkRecFldDFunOcc (has_str ++ str)
    upd_occ = mkRecFldDFunOcc (upd_str ++ str)
    get_occ = mkRecFldAxiomOcc (get_str ++ str)
    set_occ = mkRecFldAxiomOcc (set_str ++ str)

    is = FldInsts has_occ upd_occ get_occ set_occ
\end{code}
