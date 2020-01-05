{-# OPTIONS --without-K #-}

module Counterpoint where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_; not)
open import Data.Fin using (Fin; #_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_; _≡ᵇ_; _<ᵇ_; compare; _∸_; ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec using ([]; _∷_; Vec; lookup; drop; reverse)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs)

------------------------------------------------

data IntervalError : Set where
  dissonant : Interval → IntervalError

intervalCheck : Interval → Maybe IntervalError
intervalCheck i = if isConsonant i then nothing else just (dissonant i)

checkIntervals : List PitchInterval → List IntervalError
checkIntervals = mapMaybe (intervalCheck ∘ proj₂)

------------------------------------------------

data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

motion : PitchInterval → PitchInterval → Motion
motion (pitch p , interval i) (pitch q , interval j) =
  let p' = p + i; q' = q + j
  in if i ≡ᵇ j then parallel
     else (if (p ≡ᵇ q) ∨ (p' ≡ᵇ q') then oblique
           else (if p <ᵇ q then (if p' <ᵇ q' then similar  else contrary)
                 else           (if p' <ᵇ q' then contrary else similar )))

data MotionError : Set where
  parallel : PitchInterval → PitchInterval → MotionError
  similar  : PitchInterval → PitchInterval → MotionError

motionCheck : PitchInterval → PitchInterval → Maybe MotionError
motionCheck i1 i2 with motion i1 i2 | isPerfect (proj₂ i2)
motionCheck i1 i2 | contrary | _     = nothing
motionCheck i1 i2 | oblique  | _     = nothing
motionCheck i1 i2 | parallel | false = nothing
motionCheck i1 i2 | parallel | true  = just (parallel i1 i2)
motionCheck i1 i2 | similar  | false = nothing
motionCheck i1 i2 | similar  | true  = just (similar i1 i2)

checkMotion : List PitchInterval → List MotionError
checkMotion = mapMaybe (uncurry motionCheck) ∘ pairs

------------------------------------------------

data CadenceError : Set where
  notOctave : PitchInterval → CadenceError
  not2and7  : PitchInterval → PitchInterval → CadenceError

cadenceCheck : PitchInterval → PitchInterval → Maybe CadenceError
cadenceCheck pi1@(pitch p , i) pi2@(pitch q , j) =
  if j == per8
  then (if ((q + 2 ≡ᵇ p) ∧ (i == maj6) ∨ (p + 1 ≡ᵇ q) ∧ (i == min10))
        then nothing
        else just (not2and7 pi1 pi2))
  else just (notOctave pi2)

-- Perhaps this should give an error if the input list is too short.
checkCadence : List PitchInterval → Maybe CadenceError
checkCadence []               = nothing
checkCadence (_ ∷ [])         = nothing
checkCadence (p ∷ q ∷ [])     = cadenceCheck p q
checkCadence (_ ∷ p ∷ q ∷ ps) = checkCadence (p ∷ q ∷ ps)

------------------------------------------------

checkFirstSpecies : List PitchInterval → List IntervalError × List MotionError × Maybe CadenceError
checkFirstSpecies pis = checkIntervals pis , checkMotion pis , checkCadence pis

FirstSpecies : List PitchInterval → Set
FirstSpecies pis = checkFirstSpecies pis ≡ ([] , [] , nothing)

------------------------------------------------
-- Second Species

-- No parallel or similar motion towards a perfect interval across bars
motionCheck2 : (i1 : PitchInterval2) (i2 : PitchInterval2) (p : isRest i2 ≡ false) → Maybe MotionError
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

-- Step-wise motion
data StepMotion : Set where
  up1   : StepMotion
  up2   : StepMotion
  down1 : StepMotion
  down2 : StepMotion
  other : StepMotion

stepMotion : Pitch → Pitch → StepMotion
stepMotion (pitch p1) (pitch p2) =
  if p1 + 1 ≡ᵇ p2 then up1
  else (if p1 + 2 ≡ᵇ p2 then up2
        else (if p2 + 1 ≡ᵇ p1 then down1
              else (if p2 + 2 ≡ᵇ p1 then down2 else other)))

-- Check if p2 is a passing note
isPassingNote : Pitch → Pitch → Pitch → Bool
isPassingNote p1 p2 p3 with stepMotion p1 p2 | stepMotion p2 p3
isPassingNote p1 p2 p3 | up1   | up1   = true
isPassingNote p1 p2 p3 | up1   | up2   = true
isPassingNote p1 p2 p3 | up1   | _     = false
isPassingNote p1 p2 p3 | up2   | up1   = true
isPassingNote p1 p2 p3 | up2   | up2   = true
isPassingNote p1 p2 p3 | up2   | _     = false
isPassingNote p1 p2 p3 | down1 | down1 = true
isPassingNote p1 p2 p3 | down1 | down2 = true
isPassingNote p1 p2 p3 | down1 | _     = false
isPassingNote p1 p2 p3 | down2 | down1 = true
isPassingNote p1 p2 p3 | down2 | down2 = true
isPassingNote p1 p2 p3 | down2 | _     = false
isPassingNote p1 p2 p3 | other | _     = false

-- Weak beats may be dissonant if they are passing notes
data WeakCheck : Set where
  ok  : WeakCheck
  bad : Pitch → Pitch → Pitch → WeakCheck

weakCheck : (i1 : PitchInterval2) → isPair i1 ≡ true →
            (i2 : PitchInterval2) → isRest i2 ≡ false →
            WeakCheck
weakCheck (pair (p1 , interval i1a , interval i1b)) _ (hold (p2 , interval i2)) _ =
  if (not (isConsonant (interval i1b)))
  then (let p1' = transposePitch (+ i1a) p1 in
        let p2' = transposePitch (+ i1b) p1 in
        let p3' = transposePitch (+ i2)  p2 in
        if (isPassingNote p1' p2' p3') then ok else bad p1' p2' p3')
  else ok
weakCheck (pair (p1 , interval i1a , interval i1b)) _ (pair (p2 , (interval i2a , i2b))) _ =
  if (not (isConsonant (interval i1b)))
  then (let p1' = transposePitch (+ i1a) p1 in
        let p2' = transposePitch (+ i1b) p1 in
        let p3' = transposePitch (+ i2a) p2 in
        if (isPassingNote p1' p2' p3') then ok else bad p1' p2' p3')
  else ok

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
-- The second-last bar is either hold or pair
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

-- Type of second-species counterpoint
Counterpoint2 : ℕ → Set
Counterpoint2 n = Vec PitchInterval2 (suc (suc n))

dropLast : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
dropLast = reverse ∘ drop 1 ∘ reverse

-- Extract the last two intervals
extractEnding : {A : Set} {n : ℕ} → Vec A (suc (suc n)) → A × A
extractEnding (i1 ∷ i2 ∷ [])  = i1 , i2
extractEnding {n = suc n} (i ∷ c) = extractEnding {n = n} c

-- Correct second-species counterpoint
data SecondSpecies : {n : ℕ} → Counterpoint2 n → Set where
  ss : {n : ℕ} → (c : Counterpoint2 n) →
       -- beginning is valid
       beginningCheck (lookup c (# 0)) ≡ true →
       -- no rest in bars other than the first one
       (∀ (m : Fin (suc n)) → isRest (lookup (drop 1 c) m) ≡ false) →
       -- no hold in bars other than the last two
       (∀ (m : Fin n) → isRest (lookup (dropLast (dropLast c)) m) ≡ false) →
       -- strong beats are consonant
       (∀ (m : Fin (suc (suc n))) → strongCheck (lookup c m) ≡ ok) →
       -- weak beats are dissonant only if they are passing notes
       (∀ (m : Fin (suc n)) →
        let i1 = lookup (dropLast c) m in
        let i2 = lookup c (Fin.suc m) in
        (p1 : isPair i1 ≡ true) → (p2 : isRest i2 ≡ false) → weakCheck i1 p1 i2 p2 ≡ ok) →
       -- all motions across bars are valid
       (∀ (m : Fin (suc n)) → (p : isRest (lookup c (Fin.suc m)) ≡ false) →
        motionCheck2 (lookup (dropLast c) m) (lookup c (Fin.suc m)) p ≡ nothing) →
       -- ending is valid
       let i = extractEnding c in endingCheck2 (proj₁ i) (proj₂ i) ≡ ok →
       SecondSpecies c
