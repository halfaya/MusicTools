{-# OPTIONS --without-K #-}

module Util where

open import Agda.Primitive       using (Level)
open import Data.Fin             using (Fin; #_) renaming (suc to fsuc)
open import Data.List            using (List; concat; replicate; []; _∷_)
open import Data.Nat             using (ℕ; suc; _*_)
open import Data.Product         using (_×_; _,_)
open import Data.Vec             using (Vec; _∷_; []) renaming (concat to cat; replicate to rep)
open import Function             using (_∘_)
open import Relation.Nullary     using (yes; no; ¬_)
open import Relation.Unary       using (Pred; Decidable)

repeat : {ℓ : Level} {A : Set ℓ} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

repeatV : {ℓ : Level} {A : Set ℓ} {k : ℕ} → (n : ℕ) → Vec A k → Vec A (n * k)
repeatV n = cat ∘ rep {n = n}

-- return index of first element that satisfies predicate or last element if none do
findIndex : {a ℓ : Level} {A : Set a} {n : ℕ} {P : Pred A ℓ} → Decidable P → Vec A (suc n) → Fin (suc n)
findIndex _ (x ∷ [])     = # 0
findIndex P (x ∷ y ∷ ys) with P x
... | yes _ = # 0
... | no  _ = fsuc (findIndex P (y ∷ ys))


-- Returns a list of all adjacent pairs in the original list.
pairs : {ℓ : Level} {A : Set ℓ} → List A → List (A × A)
pairs []           = []
pairs (x ∷ [])     = []
pairs (x ∷ y ∷ xs) = (x , y) ∷ pairs (y ∷ xs)
