{-# OPTIONS --without-K #-}

module Interval where

open import Pitch

open import Data.Bool       using (Bool; true; false; _∨_; not)
open import Data.Integer    using (+_)
open import Data.Fin        using (toℕ)
open import Data.Nat        using (ℕ; _≡ᵇ_; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product    using (_×_; _,_; Σ)

open import Function        using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

PitchPair : Set
PitchPair = Pitch × Pitch

OrderedPitchPair : PitchPair → Set
OrderedPitchPair (pitch a , pitch b) = Σ ℕ (λ n → a + n ≡ b)

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

isPerfect : Interval → Bool
isPerfect iv =
  (i == per1)  ∨
  (i == per4)  ∨
  (i == per5)  ∨
  (i == per8)
  where i = intervalWithinOctave iv

-- Half or whole step; ignores key for now.
isStep : Interval → Bool
isStep i =
  (i == min2)  ∨
  (i == maj2)

PitchInterval : Set
PitchInterval = Pitch × Interval

pitchIntervalToPitchPair : PitchInterval → PitchPair
pitchIntervalToPitchPair (p , interval n) = (p , transposePitch (+ n)  p)

-- This may not be the best way to do the conversion.
pitchPairToInterval : (ab : PitchPair) → {_ : OrderedPitchPair ab} → Interval
pitchPairToInterval (pitch _ , pitch _) {(n , _)} = interval n

--------------------------------------------------------

-- Datatypes for second-species counterpoint
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

isPair : PitchInterval2 → Bool
isPair (pair _) = true
isPair _        = false

pitchIntervalToPitchPair2 : PitchInterval2 → PitchPair2
pitchIntervalToPitchPair2 (rest p (p' , interval n))               =
  rest p (p' , transposePitch (+ n) p')
pitchIntervalToPitchPair2 (hold (p , interval n))                  =
  hold (p , transposePitch (+ n) p)
pitchIntervalToPitchPair2 (pair (p , (interval n1 , interval n2))) =
  pair (p , (transposePitch (+ n1) p , transposePitch (+ n2) p))
