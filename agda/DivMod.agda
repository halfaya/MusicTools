{-# OPTIONS --cubical --safe #-}

module DivMod where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Data.Fin        using (Fin; toℕ; fromℕ<; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Nat        using (ℕ; zero; suc; _+_; _*_; _≤_ ; _>_; _<_; _≥_; z≤n; s≤s)
open import Data.Product    using (_×_)
open import Data.Sum        using (_⊎_; inj₁; inj₂)

open import Fin

-- From Data.Fin.Properites
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

+-assoc : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n     _       = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

≤-step : {m n : ℕ} → m ≤ n → m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

n≤1+n : (n : ℕ) → n ≤ 1 + n
n≤1+n _ = ≤-step ≤-refl

≤-pred : {m n : ℕ} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

_-_ : (n m : ℕ) → {m ≤ n} → ℕ
(n     - zero)  {z≤n}   = n
(suc n - suc m) {s≤s p} = _-_ n m {p}

_-_⟨_⟩ : (n m : ℕ) → (m ≤ n) → ℕ
_-_⟨_⟩ n m m≤n = _-_ n m {m≤n}

<-∨-≥ : (m n : ℕ) → m < n ⊎ m ≥ n
<-∨-≥ zero    zero    = inj₂ z≤n
<-∨-≥ zero    (suc n) = inj₁ (s≤s z≤n)
<-∨-≥ (suc m) zero    = inj₂ z≤n
<-∨-≥ (suc m) (suc n) with <-∨-≥ m n
... | inj₁ m<n = inj₁ (s≤s m<n)
... | inj₂ m≥n = inj₂ (s≤s m≥n)

sucn-1 : (n : ℕ) → suc n - 1 ⟨ s≤s z≤n ⟩ ≡ n
sucn-1 n = refl

-decreasing : (n m : ℕ) → (m≤n : suc m ≤ n) → (n - suc m ⟨ m≤n ⟩) < n
-decreasing (suc n) zero    (s≤s z≤n) = ≤-refl
-decreasing (suc n) (suc m) (s≤s m≤n) = ≤-trans (-decreasing n m m≤n) (n≤1+n n)

-decreasing1 : (c n m : ℕ) → (m≤n : suc m ≤ n) → (n ≤ suc c) → (n - suc m ⟨ m≤n ⟩) ≤ c
-decreasing1 c (suc n) m (s≤s m≤n) (s≤s n≤c) = ≤-trans (≤-pred (-decreasing (suc n) m (s≤s m≤n))) n≤c

lemma1 : (n m : ℕ) → {m≤n : m ≤ n} → m + (n - m ⟨ m≤n ⟩) ≡ n
lemma1 n       zero    {z≤n}   = refl
lemma1 (suc n) (suc m) {s≤s p} = cong suc (lemma1 n m {p})

lemma2 : (n m a : ℕ) → {m≤n : m ≤ n} → n - m ⟨ m≤n ⟩ ≡ a → n ≡ m + a
lemma2 n m a {m≤n} x = subst (λ y → y ≡ m + a) (lemma1 n m {m≤n} ) (cong (m +_) x)

lemma3 : (n m d r : ℕ) → {m≤n : m ≤ n} → n - m ⟨ m≤n ⟩ ≡ d * m + r → n ≡ (suc d) * m + r
lemma3 n m d r {m≤n} x = lemma2 n m (d * m + r) x ∙ sym (+-assoc m (d * m) r)

infixl 7 _div_ _mod_

record DivMod (n m : ℕ) : Type where
  constructor divMod
  field
    q       : ℕ
    r       : ℕ
    r<m     : r < m
    n=q*m+r : n ≡ q * m + r

record DivModFin (n m : ℕ) : Type where
  constructor divModFin
  field
    q       : ℕ
    r       : Fin m
    n=q*m+r : n ≡ q * m + toℕ r

divmod1 : (c n m : ℕ) → (n ≤ c) → {m > 0} → DivMod n m
divmod1 zero zero (suc m) z≤n = divMod 0 0 (s≤s z≤n) refl
divmod1 (suc c) n (suc m) n≤c with <-∨-≥ n (suc m)
... | inj₁ n<m = divMod 0 n n<m refl
... | inj₂ n≥m =
  let (divMod q r r<m n-m≡q*m+r) = divmod1 c (n - (suc m) ⟨ n≥m ⟩) (suc m) (-decreasing1 c n m n≥m n≤c ) {s≤s z≤n}
  in divMod (suc q) r r<m (lemma3 n (suc m) q r n-m≡q*m+r)

divmod : (n m : ℕ) → {m > 0} → DivMod n m
divmod n (suc m) = divmod1 n n (suc m) ≤-refl {s≤s z≤n}

_div_ : (n m : ℕ) → {m > 0} → ℕ
n div (suc m) = DivMod.q (divmod n (suc m) {s≤s z≤n})

_mod_ : (n m : ℕ) → {m > 0} → ℕ
n mod (suc m) = DivMod.r (divmod n (suc m) {s≤s z≤n})

---------

{-
dm→dmf : {m n : ℕ} → DivMod n m → DivModFin n m
dm→dmf {m} {n} (divMod q r r<m n=q*m+r) =
  divModFin q (fin1→fin (fin1 r r<m)) (subst (λ x → n ≡ q * m + x) (sym (toℕ-fromℕ< r<m)) n=q*m+r)

dmf→dm : {m n : ℕ} → DivModFin n m → DivMod n m
dmf→dm (divModFin q r n=q*m+r) = divMod q (toℕ r) (toℕ<n r) n=q*m+r

dm→dmf→dm : {m n : ℕ} → (dm : DivMod n m) → (dmf→dm ∘ dm→dmf) dm ≡ dm
dm→dmf→dm (divMod q r r<m n=q*m+r) i = divMod q (toℕ-fromℕ< r<m i) {!!} {!!}

dmf→dm→dmf : {m n : ℕ} → (dmf : DivModFin n m) → (dm→dmf ∘ dmf→dm) dmf ≡ dmf
dmf→dm→dmf (divModFin q r n=q*m+r) i = divModFin q (fromℕ<-toℕ r (toℕ<n r) i) {!!}

dm≃dmf : {n m : ℕ} → Iso (DivMod n m) (DivModFin n m)
dm≃dmf = iso dm→dmf dmf→dm dmf→dm→dmf dm→dmf→dm

dm≡dmf : {n m : ℕ} → DivMod n m ≡ DivModFin n m
dm≡dmf = isoToPath dm≃dmf
-}

---------

x1 : (n m : ℕ) {m>0 : m > 0} → _mod_ n m {m>0} < m
x1 n (suc m) = DivMod.r<m (divmod n (suc m) {s≤s z≤n})

x2 : (n m : ℕ) {m>0 : m > 0} → n ≡ (_div_ n m {m>0}) * m + (_mod_ n m {m>0})
x2 n (suc m) = DivMod.n=q*m+r (divmod n (suc m) {s≤s z≤n})

aa = divmod 73 12
bb = 73 div 12
cc = 73 mod 12


