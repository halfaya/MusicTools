{-# OPTIONS --erased-cubical --safe #-}

module Util where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
--open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Agda.Primitive       using (Level)
open import Data.Fin             using (Fin; #_; toℕ; inject; fromℕ; fromℕ<; inject₁) renaming (zero to fz; suc to fsuc)
open import Data.Bool            using (Bool; true; false; if_then_else_)
open import Data.Integer         using (ℤ; +_; -[1+_]; _-_; ∣_∣; -_)
open import Data.List            using (List; concat; replicate; []; _∷_; _∷ʳ_; map; _++_; reverse)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Nat             using (ℕ; zero; suc; _+_; _*_; _<ᵇ_; _≤ᵇ_; _≡ᵇ_; _<?_; _≟_; _∸_; _<_; s≤s; z≤n; _⊓_)
open import Data.Nat.DivMod      using (_mod_)
open import Data.Nat.Properties  using (≤-step; ≤-trans; ≤-refl)
open import Data.Product         using (_×_; _,_)
open import Data.Vec             using (Vec; _∷_; []; zip; last) renaming (concat to cat; replicate to rep; map to vmap; _∷ʳ_ to _v∷ʳ_)
open import Relation.Nullary     using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Unary       using (Pred; Decidable)

infixr 9 _∘_

_∘_ : {ℓ : Level}{A : Type ℓ}{B : A → Type ℓ}{C : (a : A) → B a → Type ℓ}
  (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

repeat : {ℓ : Level} {A : Type ℓ} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

repeatV : {ℓ : Level} {A : Type ℓ} {k : ℕ} → (n : ℕ) → Vec A k → Vec A (n * k)
repeatV n = cat ∘ rep {n = n}

-- return index of first element that satisfies predicate or last element if none do
findIndex : {a ℓ : Level} {A : Type a} {n : ℕ} {P : Pred A ℓ} → Decidable P → Vec A (suc n) → Fin (suc n)
findIndex _ (x ∷ [])     = # 0
findIndex P (x ∷ y ∷ ys) with P x
... | yes _ = # 0
... | no  _ = fsuc (findIndex P (y ∷ ys))


-- Returns a list of all adjacent pairs in the original list.
pairs : {ℓ : Level} {A : Type ℓ} → List A → List (A × A)
pairs []           = []
pairs (x ∷ [])     = []
pairs (x ∷ y ∷ xs) = (x , y) ∷ pairs (y ∷ xs)

-- Returns a list of all pairs in the original list.
allPairs : {ℓ : Level} {A : Type ℓ} → List A → List (A × A)
allPairs [] = []
allPairs (x ∷ xs) = map (x ,_) xs ++ allPairs xs

-- Returns a singleton list of the pair of the first and last element if the list has at least 2 elements,
-- or the empty list otherwise.
firstLast : {ℓ : Level} {A : Type ℓ} → List A → List (A × A)
firstLast []       = []
firstLast (x ∷ xs) with reverse xs
... | []     = []
... | y ∷ ys = (x , y) ∷ []

-- Returns a list of all adjacent pairs in the original list, prepended by the pair of the first and last elements.
◯pairs : {ℓ : Level} {A : Type ℓ} → List A → List (A × A)
◯pairs xs = firstLast xs ++ pairs xs

-- Returns a list of the first element paired with all later elements, in order.
firstPairs : {ℓ : Level} {A : Type ℓ} → List A → List (A × A)
firstPairs []       = []
firstPairs (x ∷ xs) = map (x ,_) xs

-- Basic Boolean Filter and Elem
filter : {ℓ : Level} {A : Type ℓ} → (A → Bool) → List A → List A
filter f []       = []
filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

infix 4 _∈_via_
_∈_via_ : {ℓ : Level} {A : Type ℓ} → A → List A → (A → A → Bool) → Bool
x ∈ []     via f = false
x ∈ y ∷ ys via f = if f x y then true else x ∈ ys via f

concatMaybe : {ℓ : Level} {A : Type ℓ} → List (Maybe A) → List A
concatMaybe []             = []
concatMaybe (nothing ∷ xs) = concatMaybe xs
concatMaybe (just x  ∷ xs) = x ∷ concatMaybe xs

listMin : {ℓ : Level} {A : Type ℓ} → (A → ℕ) → List A → Maybe A
listMin f [] = nothing
listMin f (x ∷ xs) with listMin f xs
... | nothing = just x
... | just y  = if f x <ᵇ f y then just x else just y

fins : (k : ℕ) → Vec (Fin k) k
fins zero    = []
fins (suc k) = fz ∷ vmap fsuc (fins k)

fins' : (n : ℕ) → (k : Fin n) → Vec (Fin n) (toℕ k)
fins' n k = vmap inject (fins (toℕ k))

finSuc : {n : ℕ} → Fin (suc n) → Fin (suc n)
finSuc {n} m with suc (toℕ m) <? suc n
... | yes x = fromℕ< x
... | no  _  = fz

_+N_ : {n : ℕ} → Fin (suc n) → ℕ → Fin (suc n)
a +N zero  = a
a +N suc b = finSuc a +N b

∣-∣helper : (n : ℕ) → ℕ → ℕ → ℕ
∣-∣helper n a b with a ≤ᵇ b
... | true  = (b ∸ a) ⊓ ((n + a) ∸ b)
... | false = (a ∸ b) ⊓ ((n + b) ∸ a)

⟨_⟩∣_-_∣ : (n : ℕ) → Fin n → Fin n → ℕ
⟨_⟩∣_-_∣ n a b = ∣-∣helper n (toℕ a) (toℕ b)

n∸k<n : (n k : ℕ) → (suc n) ∸ (suc k) < suc n
n∸k<n zero    zero    = s≤s z≤n
n∸k<n (suc n) zero    = s≤s (n∸k<n n zero)
n∸k<n zero    (suc k) = s≤s z≤n
n∸k<n (suc n) (suc k) = ≤-trans (n∸k<n n k) (≤-step ≤-refl)

opposite' : ∀ {n} → Fin n → Fin n
opposite' {suc n} fz       = fz
opposite' {suc n} (fsuc k) = fromℕ< (n∸k<n n (toℕ k))

-- opposite "i" = "n - i" (i.e. the additive inverse).
opposite : ∀ {n} → Fin n → Fin n
opposite {suc n} fz              = fz
opposite {suc n} (fsuc fz)       = fromℕ n
opposite {suc n} (fsuc (fsuc i)) = inject₁ (opposite (fsuc i))

_modℕ_ : (dividend : ℤ) (divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
((+ n)    modℕ d) {d≠0} = (n mod d) {d≠0}
(-[1+ n ] modℕ d) {d≠0} = opposite ((suc n mod d) {d≠0})

zipWithIndex : {ℓ : Level} {A : Type ℓ} {k : ℕ} → Vec A k → Vec (Fin k × A) k
zipWithIndex {k = k} = zip (fins k)

iter : {ℓ : Level} {A : Type ℓ} → (A → A) → ℕ → A → List A
iter f zero    x = x ∷ []
iter f (suc n) x = x ∷ iter f n (f x)

rotateLeft : {ℓ : Level} {A : Type ℓ} → List A → List A
rotateLeft []       = []
rotateLeft (x ∷ xs) = xs ∷ʳ x

rotateRight : {ℓ : Level} {A : Type ℓ} → List A → List A
rotateRight = reverse ∘ rotateLeft ∘ reverse

vrotateLeft : {ℓ : Level} {A : Type ℓ} {k : ℕ} → Vec A k → Vec A k
vrotateLeft {k = zero}  []       = []
vrotateLeft {k = suc k} (x ∷ xs) = xs v∷ʳ x

vrotateRight : {ℓ : Level} {A : Type ℓ} {k : ℕ} → Vec A k → Vec A k
vrotateRight {k = zero}  []          = []
vrotateRight {k = suc k} xs@(_ ∷ ys) = last xs ∷ ys
