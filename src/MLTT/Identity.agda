module MLTT.Identity where

open import Level using (Level)
open import MLTT.Universe

infix 4 _==_

-- | Martin-Lof identity type with standard path operations.
data _==_ {ell} {A : Type ell} (x : A) : A -> Type ell where
  refl : x == x

-- | Path induction (J eliminator).
J :
  forall {ell ell'} {A : Type ell} {x : A}
  (P : forall {y} -> x == y -> Type ell')
  -> P refl
  -> forall {y} (p : x == y) -> P p
J P base refl = base

-- | Transport along a path in a dependent family.
transport :
  forall {ell ell'} {A : Type ell} (P : A -> Type ell') {x y}
  -> x == y -> P x -> P y
transport P refl px = px

-- | Symmetry of equality.
sym :
  forall {ell} {A : Type ell} {x y : A} -> x == y -> y == x
sym refl = refl

-- | Transitivity / concatenation of paths.
infixl 5 _chain_
_chain_ :
  forall {ell} {A : Type ell} {x y z : A} -> x == y -> y == z -> x == z
_chain_ refl q = q

-- | Congruence for functions.
cong :
  forall {ell ell'} {A : Type ell} {B : Type ell'} (f : A -> B)
  {x y} -> x == y -> f x == f y
cong f refl = refl

-- | Congruence for dependent functions.
congDep :
  forall {ell ell'} {A : Type ell} {B : A -> Type ell'}
  (f : (x : A) -> B x) {x y} (p : x == y)
  -> transport B p (f x) == f y
congDep f refl = refl

-- | Application on both arguments of a binary function.
cong2 :
  forall {ell1 ell2 ell3}
  {A : Type ell1} {B : Type ell2} {C : Type ell3}
  (f : A -> B -> C)
  {x x'} (p : x == x')
  {y y'} (q : y == y')
  -> f x y == f x' y'
cong2 f refl refl = refl
