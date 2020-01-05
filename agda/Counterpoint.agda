{-# OPTIONS --without-K #-}

module Counterpoint where

open import Data.Bool using (true; false; if_then_else_; _∨_; _∧_)
open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₂; uncurry)
open import Data.Vec using ([]; _∷_)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

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

IsFirstSpecies : List PitchInterval → Set
IsFirstSpecies pis = checkFirstSpecies pis ≡ ([] , [] , nothing)
