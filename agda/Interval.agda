{-# OPTIONS --without-K #-}

module Interval where

open import Pitch

open import Data.Bool       using (Bool; _∨_; not)
open import Data.Integer    using (+_)
open import Data.Fin        using (toℕ)
open import Data.Nat        using (ℕ; _≡ᵇ_; _∸_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product    using (_×_; _,_)

open import Function        using (_∘_)

PitchPair : Set
PitchPair = Pitch × Pitch

data Interval : Set where
  interval : ℕ → Interval

infix 4 _==_

_==_ : Interval → Interval → Bool
(interval a) == (interval b) = a ≡ᵇ b

intervalWithinOctave : Interval → Interval
intervalWithinOctave (interval i) = interval (toℕ (i mod chromaticScaleSize))

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

-- Half or whole step; ignores key for now.
isStep : Interval → Bool
isStep i =
  (i == min2)  ∨
  (i == maj2)

PitchInterval : Set
PitchInterval = Pitch × Interval

pitchIntervalToPitchPair : PitchInterval → PitchPair
pitchIntervalToPitchPair (p , interval n) = (p , transposePitch (+ n)  p)

-- assume a ≤ b
pitchPairToInterval : PitchPair → Interval
pitchPairToInterval (pitch a , pitch b) = interval (b ∸ a)

isPerfect : Interval → Bool
isPerfect iv =
  (i == per1)  ∨
  (i == per4)  ∨
  (i == per5)  ∨
  (i == per8)
  where i = intervalWithinOctave iv
