module MLTT.Empty where

open import MLTT.Universe

-- | Empty type (no constructors).
data Empty : Type0 where

-- | Eliminator from empty type (ex falso quodlibet).
emptyRec : forall {ell} {C : Type ell} -> Empty -> C
emptyRec ()

emptyInd : forall {ell} {C : Empty -> Type ell} (p : Empty) -> C p
emptyInd ()
