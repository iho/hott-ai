module MLTT.Universe where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- | "Type" synonym following HoTT conventions.  Type ell lives one level
-- higher than its inhabitants (Agda's 'Set ell').
Type : (ell : Level) -> Set (lsuc ell)
Type ell = Set ell

Type0 : Set (lsuc lzero)
Type0 = Type lzero

Type1 : Set (lsuc (lsuc lzero))
Type1 = Type (lsuc lzero)

Type2 : Set (lsuc (lsuc (lsuc lzero)))
Type2 = Type (lsuc (lsuc lzero))

levelJoin : Level -> Level -> Level
levelJoin = _⊔_
