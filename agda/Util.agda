{-# OPTIONS --without-K #-}

module Util where

open import Agda.Primitive       using (Level)
open import Data.Fin             using (Fin; #_) renaming (suc to fsuc)
open import Data.List            using (List; concat; replicate)
open import Data.Nat             using (ℕ; suc)
open import Data.Vec             using (Vec; _∷_; [])
open import Function             using (_∘_)
open import Relation.Nullary     using (yes; no; ¬_)
open import Relation.Unary       using (Pred; Decidable)

repeat : ∀ {a} {A : Set a} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

-- return index of first element that satisfies predicate or last element if none do
findIndex : {a ℓ : Level} {A : Set a} {n : ℕ} {P : Pred A ℓ} → Decidable P → Vec A (suc n) → Fin (suc n)
findIndex _ (x ∷ [])     = # 0
findIndex P (x ∷ y ∷ ys) with P x
... | yes _ = # 0
... | no  _ = fsuc (findIndex P (y ∷ ys))

