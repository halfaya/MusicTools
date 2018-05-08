module Util where

open import Data.Nat
open import Data.Nat.Properties using (≤-step)
open import Data.Fin hiding (_≤_; _<_)

k≤n⇒n-k≤n : (k n : ℕ) → k ≤ n → n ∸ k ≤ n
k≤n⇒n-k≤n zero    zero    z≤n     = z≤n
k≤n⇒n-k≤n zero    (suc n) z≤n     = s≤s (k≤n⇒n-k≤n zero n z≤n)
k≤n⇒n-k≤n (suc k) zero    ()
k≤n⇒n-k≤n (suc k) (suc n) (s≤s p) = ≤-step (k≤n⇒n-k≤n k n p)

finN<N : {n : ℕ} → (k : Fin n) → toℕ k < n
finN<N zero    = s≤s z≤n
finN<N (suc k) = s≤s (finN<N k)

suc≤-injective : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc≤-injective (s≤s p) = p

-- revMod k = n - k
revMod : ∀ {n : ℕ} → Fin (suc n) → Fin (suc n)
revMod {n} k = fromℕ≤ (s≤s (k≤n⇒n-k≤n (toℕ k) n (suc≤-injective (finN<N k))))
