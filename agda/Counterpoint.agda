{-# OPTIONS --without-K #-}

module Counterpoint where

open import Music
open import Note
open import Pitch
open import Interval

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; pred; _+_;  _∸_; _≟_; compare; equal; less; greater)
open import Data.Integer    using (+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc)

open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Possible motion
data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

-- assume a ≤ b , c ≤ d
motion : PitchPair → PitchPair → Motion
motion (pitch a , pitch b) (pitch c , pitch d) with b ∸ a ≟ d ∸ c | compare a c | compare b d
motion (pitch a , pitch b) (pitch c , pitch d)                           | yes p | y            | z            = parallel
motion (pitch a , pitch b) (pitch .a , pitch d)                          | no ¬p | equal .a     | z            = oblique
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .(suc (b + m))) | no ¬p | less .a k    | less .b m    = similar
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .b)             | no ¬p | less .a k    | equal .b     = oblique
motion (pitch a , pitch .(suc (d + m))) (pitch .(suc (a + k)) , pitch d) | no ¬p | less .a k    | greater .d m = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .(suc (b + m))) | no ¬p | greater .c k | less .b m    = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .b)             | no ¬p | greater .c k | equal .b     = oblique
motion (pitch .(suc (c + k)) , pitch .(suc (d + m))) (pitch c , pitch d) | no ¬p | greater .c k | greater .d m = similar

-- No parallel or similar motion towards a perfect interval
data MotionCheck : Set where
  ok       : MotionCheck
  parallel : PitchInterval → PitchInterval → MotionCheck
  similar  : PitchInterval → PitchInterval → MotionCheck

motionCheck : (i1 : PitchInterval) (i2 : PitchInterval) → MotionCheck
motionCheck i1 i2 with motion (pitchIntervalToPitchPair i1) (pitchIntervalToPitchPair i2) | isPerfect (proj₂ i2)
motionCheck i1 i2 | contrary | _     = ok
motionCheck i1 i2 | oblique  | _     = ok
motionCheck i1 i2 | parallel | false = ok
motionCheck i1 i2 | parallel | true  = parallel i1 i2
motionCheck i1 i2 | similar  | false = ok
motionCheck i1 i2 | similar  | true  = similar i1 i2

--pitchToMusic : Pitch → Music
--pitchToMusic = note ∘ tone 8th

pitchPairToMusic : (d : Duration) → PitchPair → Music 2 (unduration d)
pitchPairToMusic d (p , q) = music (note→melody (tone d p) ∷ note→melody (tone d q) ∷ [])

{-
pitchIntervalToMusic : PitchInterval → Music
pitchIntervalToMusic = pitchPairToMusic ∘ pitchIntervalToPitchPair

pitchIntervalsToMusic : PitchInterval → Music
pitchIntervalsToMusic = pitchPairToMusic ∘ pitchIntervalToPitchPair
-}

-- Possible ending
data Ending : Set where
  cadence2 : Ending
  cadence7 : Ending
  other    : PitchPair → PitchPair → Ending

ending : PitchPair → PitchPair → Ending
ending (pitch a , pitch b) (pitch c , pitch d) with b ∸ a | d ∸ c
ending (pitch a , pitch b) (pitch c , pitch d) | 9  | 12 = cadence2
ending (pitch a , pitch b) (pitch c , pitch d) | 15 | 12 = cadence7
ending pp1                 pp2                 | _  | _  = other pp1 pp2

-- Ending must be cadence → octave
data EndingCheck : Set where
  ok  : EndingCheck
  bad : PitchInterval → PitchInterval → EndingCheck

endingCheck : (i1 : PitchInterval) (i2 : PitchInterval) → EndingCheck
endingCheck i1 i2 with ending (pitchIntervalToPitchPair i1) (pitchIntervalToPitchPair i2)
endingCheck i1 i2 | cadence2  = ok
endingCheck i1 i2 | cadence7  = ok
endingCheck i1 i2 | other _ _ = bad i1 i2

-- Type of counterpoint
Counterpoint : ℕ → Set
Counterpoint n = Vec PitchInterval (suc (suc n))

-- Extract the last two intervals
extractEnding : {A : Set} {n : ℕ} → Vec A (suc (suc n)) → A × A
extractEnding (i1 ∷ i2 ∷ [])  = i1 , i2
extractEnding {n = suc n} (i ∷ c) = extractEnding {n = n} c

-- Drop the last interval

foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

reverse : ∀ {a n} {A : Set a} → Vec A n → Vec A n
reverse {A = A} = foldl (Vec A) (λ rev x → x ∷ rev) []

dropLast : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
dropLast v with reverse v
dropLast v | _ ∷ xs = reverse xs

dropFirst : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
dropFirst (_ ∷ xs) = xs

-- First-species counterpoint
data FirstSpecies : {n : ℕ} → Counterpoint n → Set where
  fs : {n : ℕ} → (c : Counterpoint n) →
       -- all intervals are consonant
       (∀ (m : Fin (suc (suc n))) → isConsonant (proj₂ (lookup c m)) ≡ true) →
       -- all motions are valid
       (∀ (m : Fin (suc n)) → motionCheck (lookup (dropLast c) m) (lookup c (suc m)) ≡ ok) →
       -- ending is valid
       let i = extractEnding c in endingCheck (proj₁ i) (proj₂ i) ≡ ok →
       FirstSpecies c

-- Types for second-species counterpoint
data PitchPair2 : Set where
  rest : Pitch → Pitch × Pitch → PitchPair2
  hold : Pitch × Pitch → PitchPair2
  pair : Pitch × (Pitch × Pitch) → PitchPair2

data PitchInterval2 : Set where
  rest : Pitch → Pitch × Interval → PitchInterval2
  hold : Pitch × Interval → PitchInterval2
  pair : Pitch × (Interval × Interval) → PitchInterval2

isRest : PitchInterval2 → Bool
isRest (rest _ _) = true
isRest _          = false

isHold : PitchInterval2 → Bool
isHold (hold _) = true
isHold _        = false

pitchIntervalToPitchPair2 : PitchInterval2 → PitchPair2
pitchIntervalToPitchPair2 (rest p (p' , interval n))               =
  rest p (p' , transposePitch (+ n) p')
pitchIntervalToPitchPair2 (hold (p , interval n))                  =
  hold (p , transposePitch (+ n) p)
pitchIntervalToPitchPair2 (pair (p , (interval n1 , interval n2))) =
  pair (p , (transposePitch (+ n1) p , transposePitch (+ n2) p))

motionCheck2 : (i1 : PitchInterval2) (i2 : PitchInterval2) (p : isRest i2 ≡ false) → MotionCheck
motionCheck2 (rest p1 (p1' , i1)) (rest _ _) ()
motionCheck2 (rest p1 (p1' , i1)) (hold (p2 , i2)) refl           = motionCheck (p1' , i1) (p2 , i2) 
motionCheck2 (rest p1 (p1' , i1)) (pair (p2 , (i2 , i3))) refl    = motionCheck (p1' , i1) (p2 , i2)
motionCheck2 (hold (p1 , i1)) (rest _ _) ()
motionCheck2 (hold (p1 , i1)) (hold (p2 , i2)) refl               = motionCheck (p1 , i1) (p2 , i2)
motionCheck2 (hold (p1 , i1)) (pair (p2 , (i2 , i3))) refl        = motionCheck (p1 , i1) (p2 , i2)
motionCheck2 (pair (p1 , (i1 , i2))) (rest _ _) ()
motionCheck2 (pair (p1 , (i1 , i2))) (hold (p2 , i3)) refl        = motionCheck (p1 , i1) (p2 , i3)
motionCheck2 (pair (p1 , (i1 , i2))) (pair (p2 , (i3 , i4))) refl = motionCheck (p1 , i1) (p2 , i3)

-- Strong beats must be consonant
data StrongCheck : Set where
  ok  : StrongCheck
  bad : Interval → StrongCheck

strongCheck : PitchInterval2 → StrongCheck
strongCheck (rest _ _)     = ok
strongCheck (hold (p , i)) = if (isConsonant i) then ok else bad i
strongCheck (pair (p , (i1 , i2))) with isConsonant i1 | isConsonant i2
strongCheck (pair (p , (i1 , i2))) | b1 | b2 =
  if b1 then (if b2 then ok else bad i2) else bad i1

-- Possible beginning
beginningCheck : PitchInterval2 → Bool
beginningCheck (rest _ _)   = true
beginningCheck (hold _)     = false
beginningCheck (pair _)     = true

-- Possible ending
data Ending2 : Set where
  cadence2h : Ending2
  cadence2p : Ending2
  cadence7h : Ending2
  cadence7p : Ending2
  other     : Ending2

ending2 : PitchPair2 → PitchPair2 → Ending2
ending2 (rest _ _) _ = other
ending2 (hold (pitch a , pitch b)) (hold (pitch c , pitch d)) with b ∸ a | d ∸ c
ending2 (hold (pitch a , pitch b)) (hold (pitch c , pitch d)) | 9  | 12               = cadence2h
ending2 (hold (pitch a , pitch b)) (hold (pitch c , pitch d)) | 15 | 12               = cadence7h
ending2 (hold (pitch a , pitch b)) (hold (pitch c , pitch d)) | _  | _                = other
ending2 (pair (pitch a , (pitch b1 , pitch b2))) (hold (pitch c , pitch d)) with b2 ∸ a | d ∸ c
ending2 (pair (pitch a , (pitch b1 , pitch b2))) (hold (pitch c , pitch d)) | 9  | 12 = cadence2p
ending2 (pair (pitch a , (pitch b1 , pitch b2))) (hold (pitch c , pitch d)) | 15 | 12 = cadence7p
ending2 (pair (pitch a , (pitch b1 , pitch b2))) (hold (pitch c , pitch d)) | _  | _  = other
ending2 _  _                                                                          = other
 
-- Ending must be cadence → octave
data EndingCheck2 : Set where
  ok  : EndingCheck2
  bad : PitchInterval2 → PitchInterval2 → EndingCheck2

endingCheck2 : (i1 : PitchInterval2) (i2 : PitchInterval2) → EndingCheck2
endingCheck2 i1 i2 with ending2 (pitchIntervalToPitchPair2 i1) (pitchIntervalToPitchPair2 i2)
endingCheck2 i1 i2 | cadence2h = ok
endingCheck2 i1 i2 | cadence2p = ok
endingCheck2 i1 i2 | cadence7h = ok
endingCheck2 i1 i2 | cadence7p = ok
endingCheck2 i1 i2 | other     = bad i1 i2

-- Type of counterpoint
Counterpoint2 : ℕ → Set
Counterpoint2 n = Vec PitchInterval2 (suc (suc n))

-- Second-species counterpoint
data SecondSpecies : {n : ℕ} → Counterpoint2 n → Set where
  ss : {n : ℕ} → (c : Counterpoint2 n) →
       -- beginning is valid
       beginningCheck (lookup c zero) ≡ true →
       -- no rest in bars other than the first one
       (∀ (m : Fin (suc n)) → isRest (lookup (dropFirst c) m) ≡ false) →
       -- no hold in bars other than the last one
       (∀ (m : Fin (suc n)) → isRest (lookup (dropLast c) m) ≡ false) →
       -- strong beats are consonant
       (∀ (m : Fin (suc (suc n))) → strongCheck (lookup c m) ≡ ok) →
       -- all motions across bars are valid
       (∀ (m : Fin (suc n)) → (p : isRest (lookup c (suc m)) ≡ false) →
        motionCheck2 (lookup (dropLast c) m) (lookup c (suc m)) p ≡ ok) →
       -- ending is valid
       let i = extractEnding c in endingCheck2 (proj₁ i) (proj₂ i) ≡ ok →
       SecondSpecies c
