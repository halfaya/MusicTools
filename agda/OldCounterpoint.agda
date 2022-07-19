{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module OldCounterpoint where

open import Cubical.Core.Everything using (Type)

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_; not)
open import Data.Fin using (Fin; #_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; mapMaybe; map; zip; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_; _<ᵇ_; compare; _∸_; ℕ; zero) renaming (_≡ᵇ_ to _==_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec using ([]; _∷_; Vec; lookup; drop; reverse)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Constraint
open import Interval
open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs)

------------------------------------------------

-- First species

-- Beginning must be the 1st, 5th, or 8th
data BeginningError : Set where
  not158   : PitchInterval → BeginningError

checkBeginning : PitchInterval → Maybe BeginningError
checkBeginning pi@(_ , i) =
  if ((i == per1) ∨ (i == per5) ∨ (i == per8))
  then nothing
  else just (not158 pi)
  
------------------------------------------------

-- Intervals in middle bars must be consonant and non-unison
data IntervalError : Set where
  dissonant : Upi   → IntervalError
  unison    : Pitch → IntervalError

intervalCheck : PitchInterval → Maybe IntervalError
intervalCheck (p , i) with isConsonant i | isUnison i
intervalCheck (p , i) | false | _    = just (dissonant i)
intervalCheck (p , i) | _     | true = just (unison p)
intervalCheck (p , i) | _     | _    = nothing

checkIntervals : List PitchInterval → List IntervalError
checkIntervals = mapMaybe intervalCheck

------------------------------------------------

-- Perfect intervals must not approached by parallel or similar motion
data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

motion : PitchInterval → PitchInterval → Motion
motion (p , i) (q , j) =
  let p' = p + i; q' = q + j
  in if i == j then parallel
     else (if (p == q) ∨ (p' == q') then oblique
           else (if p <ᵇ q then (if p' <ᵇ q' then similar  else contrary)
                 else           (if p' <ᵇ q' then contrary else similar)))

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

-- Ending must be the 1st or 8th approached by a cadence
data EndingError : Set where
  not18    : PitchInterval → EndingError
  not27    : PitchInterval → EndingError
  tooShort : List PitchInterval → EndingError

endingCheck : PitchInterval → PitchInterval → Maybe EndingError
endingCheck pi1@(p , i) (q , 0)  = 
  if ((p + 1 == q) ∧ (i == min3)) then nothing else just (not27 pi1)
endingCheck pi1@(p , i) (q , 12) =
  if ((q + 2 == p) ∧ (i == maj6) ∨ (p + 1 == q) ∧ (i == min10))
  then nothing
  else just (not27 pi1)
endingCheck pi1               pi2                     =
  just (not18 pi2)

checkEnding : List PitchInterval → PitchInterval → Maybe EndingError
checkEnding []       _ = just (tooShort [])
checkEnding (p ∷ []) q = endingCheck p q
checkEnding (p ∷ ps) q = checkEnding ps q

------------------------------------------------

-- Correct first species counterpoint
record FirstSpecies : Set where
  constructor firstSpecies
  field
    firstBar    : PitchInterval
    middleBars  : List PitchInterval
    lastBar     : PitchInterval
    beginningOk : checkBeginning firstBar ≡ nothing
    intervalsOk : checkIntervals middleBars ≡ []
    motionOk    : checkMotion (firstBar ∷ middleBars) ≡ []
                  -- no need to include the last bar,
                  -- since endingOK guarantees contrary motion in the ending
    endingOk    : checkEnding middleBars lastBar ≡ nothing

------------------------------------------------
-- Second Species

PitchInterval2 : Set
PitchInterval2 = Pitch × Upi × Upi

strongBeat : PitchInterval2 → PitchInterval
strongBeat (p , i , _) = p , i

weakBeat : PitchInterval2 → PitchInterval
weakBeat (p , _ , i) = p , i

expandPitchInterval2 : PitchInterval2 → List PitchInterval
expandPitchInterval2 (p , i , j) = (p , i) ∷ (p , j) ∷ []

expandPitchIntervals2 : List PitchInterval2 → List PitchInterval
expandPitchIntervals2 = concatMap expandPitchInterval2

------------------------------------------------

-- Beginning must be the 5th or 8th
data BeginningError2 : Set where
  not58    : PitchInterval → BeginningError2

checkBeginning2 : PitchInterval → Maybe BeginningError2
checkBeginning2 pi@(_ , i) =
  if ((i == per5) ∨ (i == per8))
  then nothing
  else just (not58 pi)

checkEnding2 : List PitchInterval2 → PitchInterval → Maybe EndingError
checkEnding2 []           _   = just (tooShort [])
checkEnding2 (p ∷ [])     q   = endingCheck (weakBeat p) q
checkEnding2 (_ ∷ p ∷ ps) q   = checkEnding2 (p ∷ ps) q

------------------------------------------------

-- Strong beats must be consonant and non-unison
checkStrongBeats : List PitchInterval2 → List IntervalError
checkStrongBeats = checkIntervals ∘ map strongBeat

------------------------------------------------

-- Weak beats may be dissonant or unison
checkWeakBeat : PitchInterval2 → Pitch → Maybe IntervalError
checkWeakBeat (p , i , j) q with isConsonant j | isUnison j 
checkWeakBeat (p , i , j) q | false | _ =
  if isPassingTone (secondPitch (p , i)) (secondPitch (p , j)) q
  then nothing
  else just (dissonant j)
checkWeakBeat (p , i , j) q | _ | true =
  if isOppositeStep (secondPitch (p , i)) (secondPitch (p , j)) q
  then nothing
  else just (unison p)
checkWeakBeat (p , i , j) q | _ | _    =
  nothing
 
checkWeakBeats : List PitchInterval2 → Pitch → List IntervalError
checkWeakBeats []            p = []
checkWeakBeats pis@(_ ∷ qis) p =
  mapMaybe (uncurry checkWeakBeat)
           (zip pis
                (map (λ {(q , i , j) → proj₂ (pitchIntervalToPitchPair (q , i))}) qis ++ (p ∷ [])))

------------------------------------------------

-- Perfect intervals on strong beats must not be approached by parallel or similar motion
checkMotion2 : List PitchInterval → List MotionError
checkMotion2 []           = []
checkMotion2 (_ ∷ [])     = []
checkMotion2 (p ∷ q ∷ ps) = checkMotion (p ∷ q ∷ []) ++ checkMotion2 ps

------------------------------------------------

-- Correct second species counterpoint
record SecondSpecies : Set where
  constructor secondSpecies
  field
    firstBar      : PitchInterval -- require counterpont to start with a rest, which is preferred
    middleBars    : List PitchInterval2
    lastBar       : PitchInterval -- require counterpoint to end with only a single whole note, which is preferred
    beginningOk   : checkBeginning2 firstBar ≡ nothing
    strongBeatsOk : checkStrongBeats middleBars ≡ []
    weakBeatsOk   : checkWeakBeats middleBars (secondPitch lastBar) ≡ []
    motionOk      : checkMotion2 (firstBar ∷ (expandPitchIntervals2 middleBars)) ≡ []
    endingOk      : checkEnding2 middleBars lastBar ≡ nothing
