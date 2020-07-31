{-# OPTIONS --without-K --safe #-}

module Util where

open import Agda.Primitive       using (Level)
open import Data.Fin             using (Fin; #_; toℕ; inject) renaming (zero to fz; suc to fsuc)
open import Data.Bool            using (Bool; true; false; if_then_else_)
open import Data.List            using (List; concat; replicate; []; _∷_)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Nat             using (ℕ; zero; suc; _*_; _<ᵇ_)
open import Data.Product         using (_×_; _,_)
open import Data.Vec             using (Vec; _∷_; []; map; zip) renaming (concat to cat; replicate to rep)
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

-- Basic Boolean Filter and Elem
filter : {ℓ : Level} {A : Set ℓ} → (A → Bool) → List A → List A
filter f []       = []
filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

infix 4 _∈_via_
_∈_via_ : {ℓ : Level} {A : Set ℓ} → A → List A → (A → A → Bool) → Bool
x ∈ []     via f = false
x ∈ y ∷ ys via f = if f x y then true else x ∈ ys via f

concatMaybe : {ℓ : Level} {A : Set ℓ} → List (Maybe A) → List A
concatMaybe []             = []
concatMaybe (nothing ∷ xs) = concatMaybe xs
concatMaybe (just x  ∷ xs) = x ∷ concatMaybe xs

listMin : {ℓ : Level} {A : Set ℓ} → (A → ℕ) → List A → Maybe A
listMin f [] = nothing
listMin f (x ∷ xs) with listMin f xs
... | nothing = just x
... | just y  = if f x <ᵇ f y then just x else just y

fins : (k : ℕ) → Vec (Fin k) k
fins zero    = []
fins (suc k) = fz ∷ map fsuc (fins k)

fins' : (n : ℕ) → (k : Fin n) → Vec (Fin n) (toℕ k)
fins' n k = map inject (fins (toℕ k))

zipWithIndex : {ℓ : Level} {A : Set ℓ} {k : ℕ} → Vec A k → Vec (Fin k × A) k
zipWithIndex {k = k} = zip (fins k)
