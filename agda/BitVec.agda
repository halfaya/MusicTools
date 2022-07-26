{-# OPTIONS --erased-cubical --safe -W noNoEquivWhenSplitting #-}

module BitVec where

open import Prelude hiding (_==_)

open import Data.String     using (fromList)

-- Bit vector representation of finite sets

BitVec : ℕ → Type
BitVec = Vec Bool

show : {n : ℕ} → BitVec n → String
show = fromList ∘ toList ∘ vmap (λ {true → '1' ; false → '0'})

empty : {n : ℕ} → BitVec n
empty = rep false

insert : {n : ℕ} → Fin n → BitVec n → BitVec n
insert k s = s [ k ]%= (λ _ → true)

infixr 5 _∪_
_∪_ : {n : ℕ} → BitVec n → BitVec n → BitVec n
_∪_ = zipWith _∨_

infixr 6 _∩_
_∩_ : {n : ℕ} → BitVec n → BitVec n → BitVec n
_∩_ = zipWith _∧_

infix 4 _∈_
_∈_ : {n : ℕ} → Fin n → BitVec n → Bool
b ∈ bv = lookup bv b

indices : {n : ℕ} → Vec (Fin n) n
indices {ℕ.zero} = []
indices {suc n} = Fin.zero ∷ vmap Fin.suc (indices {n})

elements : {n : ℕ} → BitVec n → List (Fin n)
elements {n} bv = foldr f [] (toList (vzip bv indices))
  where f : Bool × Fin n → List (Fin n) → List (Fin n)
        f (false , _) xs = xs
        f (true  , x) xs = x ∷ xs

_==_ : {n : ℕ} → BitVec n → BitVec n → Bool
[]          == []            = true
(false ∷ xs) == (false ∷ ys) = xs == ys
(false ∷ xs) == (true  ∷ ys) = false
(true  ∷ xs) == (false ∷ ys) = false
(true  ∷ xs) == (true  ∷ ys) = xs == ys
