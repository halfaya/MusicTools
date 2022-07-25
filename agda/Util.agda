{-# OPTIONS --erased-cubical --safe -W noNoEquivWhenSplitting #-}

module Util where

open import Prelude

open import Data.Integer public  using () renaming (_≤ᵇ_ to _≤ℤ_)
open import Data.Nat             using (_<_; _<ᵇ_)
open import Data.Nat.Properties  using (≤-step; ≤-trans; ≤-refl)
open import Relation.Nullary.Decidable using (False)
open import Relation.Nullary     using (yes; no; ¬_)
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
... | no  _ = fs (findIndex P (y ∷ ys))


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

-- Basic boolean Filter and Elem
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
fins (suc k) = fz ∷ vmap fs (fins k)

fins' : (n : ℕ) → (k : Fin n) → Vec (Fin n) (toℕ k)
fins' n k = vmap (inject {n} {k}) (fins (toℕ k))

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
opposite' {suc n} (fs k) = fromℕ< (n∸k<n n (toℕ k))

-- opposite "i" = "n - i" (i.e. the additive inverse).
opposite : ∀ {n} → Fin n → Fin n
opposite {suc n} fz          = fz
opposite {suc n} (fs fz)     = fromℕ n
opposite {suc n} (fs (fs i)) = inject₁ (opposite (fs i))

_modℕ'_ : (dividend : ℤ) (divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
((+ n)    modℕ' d) {d≠0} = (n mod d) {d≠0}
(-[1+ n ] modℕ' d) {d≠0} = opposite ((suc n mod d) {d≠0})

zipWithIndex : {ℓ : Level} {A : Type ℓ} {k : ℕ} → Vec A k → Vec (Fin k × A) k
zipWithIndex {k = k} = vzip (fins k)

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

-- Integer boolean equality

infix  4 _≠ℕ_ _==ℤ_ _≠ℤ_ _<ℤ_

_≠ℕ_ : ℕ → ℕ → Bool
zero  ≠ℕ zero  = false
zero  ≠ℕ suc b = true
suc a ≠ℕ zero  = true
suc a ≠ℕ suc b = a ≠ℕ b

_==ℤ_ : ℤ → ℤ → Bool
+_     a ==ℤ +_     b = a == b
+_     a ==ℤ -[1+_] b = false
-[1+_] a ==ℤ +_     b = false
-[1+_] a ==ℤ -[1+_] b = a == b

_≠ℤ_ : ℤ → ℤ → Bool
+_     a ≠ℤ +_     b = a ≠ℕ b
+_     a ≠ℤ -[1+_] b = true
-[1+_] a ≠ℤ +_     b = true
-[1+_] a ≠ℤ -[1+_] b = a ≠ℕ b

_<ℤ_ : ℤ → ℤ → Bool
+_     a <ℤ +_     b = a <ᵇ b
+_     a <ℤ -[1+_] b = false
-[1+_] a <ℤ +_     b = true
-[1+_] a <ℤ -[1+_] b = b <ᵇ a
