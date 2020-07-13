{-# OPTIONS --without-K --safe #-}

module Interval where

open import Pitch

open import Data.Bool       using (Bool; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Integer    using (+_; _-_; sign; ∣_∣; -_)
open import Data.Fin        using (toℕ)
open import Data.Nat        using (ℕ; _≡ᵇ_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product    using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sign       using (Sign)

open import Function        using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

PitchPair : Set
PitchPair = Pitch × Pitch

data Interval : Set where
  interval : ℕ → Interval

infix 4 _==_

_==_ : Interval → Interval → Bool
(interval a) == (interval b) = a ≡ᵇ b

intervalWithinOctave : Interval → Interval
intervalWithinOctave (interval i) = interval (toℕ (i mod chromaticScaleSize))

SignedInterval : Set
SignedInterval = Sign × Interval

-- Names for intervals
per1  = interval 0
min2  = interval 1
maj2  = interval 2
min3  = interval 3
maj3  = interval 4
per4  = interval 5
aug4  = interval 6
per5  = interval 7
min6  = interval 8
maj6  = interval 9
min7  = interval 10
maj7  = interval 11
per8  = interval 12
min9  = interval 13
maj9  = interval 14
min10 = interval 15
maj10 = interval 16
per11 = interval 17
aug11 = interval 18
per12 = interval 19

isConsonant : Interval → Bool
isConsonant iv =
  (i == per1)  ∨
  (i == min3)  ∨
  (i == maj3)  ∨
  (i == per5)  ∨
  (i == min6)  ∨
  (i == maj6)  ∨
  (i == per8)
  where i = intervalWithinOctave iv

isDissonant : Interval → Bool
isDissonant = not ∘ isConsonant

isPerfect : Interval → Bool
isPerfect iv =
  (i == per1)  ∨
  (i == per4)  ∨
  (i == per5)  ∨
  (i == per8)
  where i = intervalWithinOctave iv

isUnison : Interval → Bool
isUnison i = i == per1

isThird : Interval → Bool
isThird i = (i == min3) ∨ (i == maj3)

-- Half or whole step; ignores key for now.
isStep : Interval → Bool
isStep i =
  (i == min2)  ∨
  (i == maj2)

PitchInterval : Set
PitchInterval = Pitch × Interval

pitchIntervalToPitchPair : PitchInterval → PitchPair
pitchIntervalToPitchPair (p , interval n) = (p , transposePitch (+ n)  p)

secondPitch : PitchInterval → Pitch
secondPitch = proj₂ ∘ pitchIntervalToPitchPair

pitchPairToSignedInterval : PitchPair → SignedInterval
pitchPairToSignedInterval (pitch p , pitch q) =
  let d = (+ q) - (+ p)
  in sign d , interval ∣ d ∣

-- Assumes p ≤ q
pitchPairToPitchInterval : PitchPair → PitchInterval
pitchPairToPitchInterval pq = proj₁ pq , proj₂ (pitchPairToSignedInterval pq)

stepUp : Pitch → Pitch → Bool
stepUp p q with pitchPairToSignedInterval (p , q)
... | Sign.- , _ = false
... | Sign.+ , i = isStep i

stepDown : Pitch → Pitch → Bool
stepDown p q with pitchPairToSignedInterval (p , q)
... | Sign.- , i = isStep i
... | Sign.+ , _ = false

-- Check if q is a passing tone between p and r
-- The interval between end points need to be a 3rd
isPassingTone : Pitch → Pitch → Pitch → Bool
isPassingTone p q r =
  (stepUp p q ∧ stepUp q r) ∨ (stepDown p q ∧ stepDown q r) ∨
  (isThird (proj₂ (pitchPairToSignedInterval (p , r))))

moveUp : Pitch → Pitch → Bool
moveUp p q with pitchPairToSignedInterval (p , q)
... | Sign.- , _ = false
... | Sign.+ , i = true

moveDown : Pitch → Pitch → Bool
moveDown p q with pitchPairToSignedInterval (p , q)
... | Sign.- , i = true
... | Sign.+ , _ = false

-- Check if q is left by step in the opposite direction from its approach
isOppositeStep : Pitch → Pitch → Pitch → Bool
isOppositeStep p q r = (moveUp p q ∧ stepDown q r) ∨ (moveDown p q ∧ stepUp q r)

transposePitchUp : Interval → Pitch → Pitch
transposePitchUp (interval i) p = transposePitch (+ i) p

transposePitchDown : Interval → Pitch → Pitch
transposePitchDown (interval i) p = transposePitch (- (+ i)) p

