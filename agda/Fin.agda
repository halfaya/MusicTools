{-# OPTIONS --cubical --safe #-}

module Fin where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Fin   using (Fin; toℕ; fromℕ<; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Nat   using (ℕ; zero; suc; _<_; _>_; z≤n; s≤s)

-- Alternate representation of Fin as a number and proof of its upper bound.
record Fin1 (n : ℕ) : Type where
  constructor fin1
  field
    r   : ℕ
    r<n : r < n

fin1suc : {n : ℕ} → Fin1 n → Fin1 (suc n)
fin1suc (fin1 r r<n) = fin1 (suc r) (s≤s r<n)

-- From Data.Fin.Properites
-- They need to be re-defined here since Cubical uses a different ≡

fromℕ<-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i < m) → fromℕ< i<m ≡ i
fromℕ<-toℕ fz     (s≤s z≤n)       = refl
fromℕ<-toℕ (fs i) (s≤s (s≤s m≤n)) = cong fs (fromℕ<-toℕ i (s≤s m≤n))

toℕ-fromℕ< : ∀ {m n} (m<n : m < n) → toℕ (fromℕ< m<n) ≡ m
toℕ-fromℕ< (s≤s z≤n)       = refl
toℕ-fromℕ< (s≤s (s≤s m<n)) = cong suc (toℕ-fromℕ< (s≤s m<n))

toℕ<n : ∀ {n} (i : Fin n) → toℕ i < n
toℕ<n fz     = s≤s z≤n
toℕ<n (fs i) = s≤s (toℕ<n i)


-------------------
-- Equivalence of Fin and Fin1
    
fin→fin1 : {n : ℕ} → Fin n → Fin1 n
fin→fin1 fz     = fin1 0 (s≤s z≤n)
fin→fin1 (fs x) = let fin1 r r<n = fin→fin1 x in fin1 (suc r) (s≤s r<n)

fin1→fin : {n : ℕ} → Fin1 n → Fin n
fin1→fin (fin1 _ r<n) = fromℕ< r<n

fin→fin1→fin : {n : ℕ} → (r : Fin n) → (fin1→fin ∘ fin→fin1) r ≡ r
fin→fin1→fin fz     = refl
fin→fin1→fin (fs r) = cong fs (fin→fin1→fin r)

fin1→fin→fin1 : {n : ℕ} → (r : Fin1 n) → (fin→fin1 ∘ fin1→fin) r ≡ r
fin1→fin→fin1 (fin1 zero    (s≤s z≤n))       = refl
fin1→fin→fin1 (fin1 (suc r) (s≤s (s≤s r<n))) = cong fin1suc (fin1→fin→fin1 (fin1 r (s≤s r<n)))
  
fin≃fin1 : {n : ℕ} → Iso (Fin n) (Fin1 n)
fin≃fin1 = iso fin→fin1 fin1→fin fin1→fin→fin1 fin→fin1→fin

fin≡fin1 : {n : ℕ} → Fin n ≡ Fin1 n
fin≡fin1 = isoToPath fin≃fin1

-- Equivalence of toℕ and Fin1.r

toℕ≡Fin1r1 : {n : ℕ} → (r : Fin n) → toℕ r ≡ Fin1.r (fin→fin1 r)
toℕ≡Fin1r1 fz     = refl
toℕ≡Fin1r1 (fs r) = cong suc (toℕ≡Fin1r1 r)

toℕ≡Fin1r : {n : ℕ} → toℕ {n} ≡ Fin1.r ∘ fin→fin1
toℕ≡Fin1r = funExt toℕ≡Fin1r1

Fin1r≡toℕ1 : {n : ℕ} → (r : Fin1 n) → toℕ (fin1→fin r) ≡ Fin1.r r
Fin1r≡toℕ1 (fin1 r r<n) = toℕ-fromℕ< r<n

Fin1r≡toℕ : {n : ℕ} → toℕ {n} ∘ fin1→fin ≡ Fin1.r
Fin1r≡toℕ = funExt Fin1r≡toℕ1
