module MLTT.PiSigma where

open import MLTT.Universe

-- | Dependent function space Pi with an explicit name and universe level.
Pi :
  forall {ell1 ell2}
  (A : Type ell1) (B : A -> Type ell2)
  -> Type (levelJoin ell1 ell2)
Pi A B = (x : A) -> B x

-- | Dependent pair type Sigma, written as a record to expose projections.
record Sigma {ell1 ell2} (A : Type ell1) (B : A -> Type ell2) :
  Type (levelJoin ell1 ell2) where
  constructor pair
  field
    first : A
    second : B first

open Sigma public

-- | First projection (explicit name).
pi1 :
  forall {ell1 ell2} {A : Type ell1} {B : A -> Type ell2}
  -> Sigma A B -> A
pi1 = Sigma.first

-- | Second projection (explicit name).
pi2 :
  forall {ell1 ell2} {A : Type ell1} {B : A -> Type ell2}
  -> (p : Sigma A B) -> B (pi1 p)
pi2 = Sigma.second

-- | Map a dependent pair by supplying functions for each component.
mapSigma :
  forall {ell1 ell2 ell1' ell2'}
    {A : Type ell1} {B : A -> Type ell2}
    {A' : Type ell1'} {B' : A' -> Type ell2'}
  -> (f : A -> A')
  -> (g : forall {x} -> B x -> B' (f x))
  -> Sigma A B -> Sigma A' B'
mapSigma f g (pair x y) = pair (f x) (g y)
