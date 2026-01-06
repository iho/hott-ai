module MLTT.List where

open import MLTT.Universe
open import MLTT.Nat
open import MLTT.PiSigma
open import MLTT.Bool using (Bool; false; true; if_then_else_)
open import MLTT.Unit using (Unit; tt)

infixr 5 _::_

data List {ell} (A : Type ell) : Type ell where
  []   : List A
  _::_ : A -> List A -> List A

-- | Right fold (recursor) for lists.
foldr : forall {ell ell'} {A : Type ell} {B : Type ell'}
  -> (A -> B -> B)
  -> B
  -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

map : forall {ell ell'} {A : Type ell} {B : Type ell'}
  -> (A -> B)
  -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

append : forall {ell} {A : Type ell} -> List A -> List A -> List A
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

length : forall {ell} {A : Type ell} -> List A -> Nat
length [] = zero
length (_ :: xs) = suc (length xs)

-- | Dependent predicate: all elements satisfy a property.
All : forall {ell ell'} {A : Type ell}
  -> (A -> Type ell')
  -> List A -> Type ell'
All P [] = Unit
All P (x :: xs) = Sigma (P x) (\ _ -> All P xs)

allMap : forall {ell ell'} {A : Type ell} {P : A -> Type ell'}
  -> (xs : List A)
  -> All P xs
  -> All P (map (\ x -> x) xs)
allMap [] proof = proof
allMap (x :: xs) (pair px rest) = pair px (allMap xs rest)

-- | Non-empty lists as Sigma A (lambda _ -> List A).
NonEmpty : forall {ell} {A : Type ell} -> Type ell
NonEmpty {A} = Sigma A (\ _ -> List A)

nonEmptyHead : forall {ell} {A : Type ell} -> NonEmpty {A = A} -> A
nonEmptyHead = pi1

nonEmptyTail : forall {ell} {A : Type ell} (xs : NonEmpty {A = A}) -> List A
nonEmptyTail = pi2

ListView : forall {ell} {A : Type ell} -> Type (levelJoin Type0 ell)
ListView {A} = Sigma Bool (\ b -> if b then NonEmpty {A = A} else Unit)

viewList : forall {ell} {A : Type ell} -> List A -> ListView
viewList [] = pair false tt
viewList (x :: xs) = pair true (pair x xs)
