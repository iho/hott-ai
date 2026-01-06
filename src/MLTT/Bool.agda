module MLTT.Bool where

open import MLTT.Universe

-- | Boolean type with two inhabitants.
data Bool : Type0 where
  false true : Bool

-- | Non-dependent eliminator.
boolRec : forall {ell} (C : Type ell) -> C -> C -> Bool -> C
boolRec C cf ct false = cf
boolRec C cf ct true  = ct

-- | Dependent eliminator.
boolInd : forall {ell} {C : Bool -> Type ell}
  -> C false
  -> C true
  -> (b : Bool) -> C b
boolInd cf ct false = cf
boolInd cf ct true  = ct

-- | Conditional expression.
if_then_else_ : forall {ell} {A : Type ell} -> Bool -> A -> A -> A
if false then a else b = b
if true  then a else b = a

not : Bool -> Bool
not false = true
not true  = false

infixl 4 _&&_ _||_

_&&_ : Bool -> Bool -> Bool
false && _ = false
true  && b = b

_||_ : Bool -> Bool -> Bool
false || b = b
true  || _ = true
