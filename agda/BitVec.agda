{-# OPTIONS --without-K --safe #-}

module BitVec where

open import Data.Bool       using (Bool; false; true; _∨_; _∧_)
open import Data.Fin        using (Fin; toℕ)
open import Data.List       using (List; []; _∷_; foldr)
open import Data.Nat        using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product    using (_×_; _,_; proj₂)
open import Data.String     using (String; fromList)
open import Data.Vec        using (Vec; []; _∷_; map; lookup; replicate; _[_]%=_; toList; zip; zipWith)

open import Function        using (_∘_)

-- Bit vector representation of finite sets

BitVec : ℕ → Set
BitVec = Vec Bool

show : {n : ℕ} → BitVec n → String
show = fromList ∘ toList ∘ map (λ {true → '1' ; false → '0'})

empty : {n : ℕ} → BitVec n
empty = replicate false

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
indices {suc n} = Fin.zero ∷ map Fin.suc (indices {n})

elements : {n : ℕ} → BitVec n → List (Fin n)
elements {n} bv = foldr f [] (toList (zip bv indices))
  where f : Bool × Fin n → List (Fin n) → List (Fin n)
        f (false , _) xs = xs
        f (true  , x) xs = x ∷ xs
