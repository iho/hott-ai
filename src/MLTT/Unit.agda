module MLTT.Unit where

open import MLTT.Universe

-- | Unit type with its single inhabitant.
data Unit : Type0 where
  tt : Unit

-- | Non-dependent eliminator (recursion principle).
unitRec : forall {ell} (C : Type ell) -> C -> Unit -> C
unitRec C c tt = c

-- | Dependent eliminator (induction principle).
unitInd : forall {ell} {C : Unit -> Type ell} -> C tt -> (x : Unit) -> C x
unitInd base tt = base
