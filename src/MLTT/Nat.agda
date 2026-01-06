module MLTT.Nat where

open import MLTT.Universe
open import MLTT.Identity

-- | Natural numbers with zero and successor.
data Nat : Type0 where
  zero : Nat
  suc  : Nat -> Nat

-- | Non-dependent recursion principle.
natRec : forall {ell}
  (C : Type ell)
  -> C
  -> (Nat -> C -> C)
  -> Nat -> C
natRec C base step zero    = base
natRec C base step (suc n) = step n (natRec C base step n)

-- | Dependent induction principle.
natInd : forall {ell}
  {C : Nat -> Type ell}
  -> C zero
  -> (forall n -> C n -> C (suc n))
  -> (n : Nat) -> C n
natInd cz cs zero    = cz
natInd cz cs (suc n) = cs n (natInd cz cs n)

infixl 6 _+_

-- | Addition defined by recursion on the left argument.
_+_ : Nat -> Nat -> Nat
zero  + n = n
suc m + n = suc (m + n)

-- | Right identity: n + zero == n.
RightId : Nat -> Type0
RightId n = n + zero == n

plusZeroRight : (n : Nat) -> RightId n
plusZeroRight zero    = refl
plusZeroRight (suc n) = cong suc (plusZeroRight n)

-- | Naturality of the right-identity proof under transport.
plusZeroRightTransport :
  {n m : Nat} (p : n == m)
  -> transport RightId p (plusZeroRight n) == plusZeroRight m
plusZeroRightTransport refl = refl

-- | Associativity witness (optional example).
plusAssoc : (a b c : Nat) -> (a + b) + c == a + (b + c)
plusAssoc zero b c = refl
plusAssoc (suc a) b c =
  cong suc (plusAssoc a b c)
