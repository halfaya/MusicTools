{-# OPTIONS --erased-cubical --safe #-}

open import Data.Nat        using (ℕ; zero; suc; _+_; _*_; _≤_ ; _>_; _<_; _≥_; z≤n; s≤s)
open import Data.Sum        using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Nat where

-- Useful functions for natural numbers

_-_ : (n m : ℕ) → {m ≤ n} → ℕ
(n     - zero)  {z≤n}   = n
(suc n - suc m) {s≤s p} = _-_ n m {p}

_-_⟨_⟩ : (n m : ℕ) → (m ≤ n) → ℕ
_-_⟨_⟩ n m m≤n = _-_ n m {m≤n}

m+n-m=n : (m n : ℕ) → {m≤n : m ≤ n} → m + (n - m ⟨ m≤n ⟩) ≡ n
m+n-m=n zero    n       {z≤n}     = refl
m+n-m=n (suc m) (suc n) {s≤s m≤n} = cong suc (m+n-m=n m n {m≤n})

<-∨-≥ : (m n : ℕ) → m < n ⊎ m ≥ n
<-∨-≥ zero    zero    = inj₂ z≤n
<-∨-≥ zero    (suc n) = inj₁ (s≤s z≤n)
<-∨-≥ (suc m) zero    = inj₂ z≤n
<-∨-≥ (suc m) (suc n) with <-∨-≥ m n
... | inj₁ m<n = inj₁ (s≤s m<n)
... | inj₂ m≥n = inj₂ (s≤s m≥n)
