module Util where

open import Data.List using (List; concat; replicate)
open import Data.Nat  using  (ℕ; _*_)
open import Function  using (_∘_)

open import Note

repeat : ∀ {a} {A : Set a} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

-- duration in 8th notes
16th 8th whole : ℕ → Duration
16th  n = duration n
8th   n = duration (2 * n)
whole n = duration (16 * n)
