{-# OPTIONS --without-K #-}

module Counterpoint where

open import Pitch

open import Data.Bool hiding (_≟_)
open import Data.Integer.Base using (+_;  -[1+_])-- hiding (_+_)
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

Interval : Set
Interval = Pitch × Pitch

-- allowed intervals only
data IntervalQuality : Set where
  min3 : IntervalQuality
  maj3 : IntervalQuality
  per5 : IntervalQuality
  min6 : IntervalQuality
  maj6 : IntervalQuality
  per8 : IntervalQuality
  min10 : IntervalQuality
  maj10 : IntervalQuality

PitchInterval : Set
PitchInterval = Pitch × IntervalQuality

pitchIntervalToInterval : PitchInterval → Interval
pitchIntervalToInterval (p , min3) = {!!}
pitchIntervalToInterval (p , maj3) = {!!}
pitchIntervalToInterval (p , per5) = {!!}
pitchIntervalToInterval (p , min6) = {!!}
pitchIntervalToInterval (p , maj6) = {!!}
pitchIntervalToInterval (p , per8) = {!!}
pitchIntervalToInterval (p , min10) = {!!}
pitchIntervalToInterval (p , maj10) = {!!}

isPerfect : IntervalQuality → Bool
isPerfect min3 = false
isPerfect maj3 = false
isPerfect per5 = true
isPerfect min6 = false
isPerfect maj6 = false
isPerfect per8 = true
isPerfect min10 = true
isPerfect maj10 = true

-- assume a ≥ b
isPerfectInterval : Interval → Bool
isPerfectInterval (pitch a , pitch b) =
  let d = a ∸ b
  in if d ≡ᵇ 7 then true else if d ≡ᵇ 12 then true else false

data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

-- assume a ≥ b , c ≥ d
motion : Interval → Interval → Motion
motion (pitch a , pitch b) (pitch c , pitch d) with a ∸ b ≟ c ∸ d | compare a c | compare b d
motion (pitch a , pitch b) (pitch c , pitch d) | yes p | y | z = parallel
motion (pitch a , pitch b) (pitch .a , pitch d) | no ¬p | equal .a | z = oblique
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .(suc (b + k₁))) | no ¬p | less .a k | less .b k₁ = similar
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .b) | no ¬p | less .a k | equal .b = oblique
motion (pitch a , pitch .(suc (d + k₁))) (pitch .(suc (a + k)) , pitch d) | no ¬p | less .a k | greater .d k₁ = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .(suc (b + k₁))) | no ¬p | greater .c k | less .b k₁ = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .b) | no ¬p | greater .c k | equal .b = oblique
motion (pitch .(suc (c + k)) , pitch .(suc (d + k₁))) (pitch c , pitch d) | no ¬p | greater .c k | greater .d k₁ = similar

-- contrary/oblique other has overlapping constructors
data MotionOk (i1 : Interval) (i2 : Interval) : Set where
  other    : isPerfectInterval i2 ≡ true → MotionOk i1 i2
  contrary : motion i1 i2 ≡ contrary → MotionOk i1 i2
  oblique  : motion i1 i2 ≡ oblique → MotionOk i1 i2

data FirstSpecies : List⁺ PitchInterval → Set where
  cadence2 : (p : Pitch) → FirstSpecies ((transpose (+ 2) p , maj6) ∷⁺ [ p , per8 ])
  cadence7 : (p : Pitch) → FirstSpecies ((transpose -[1+ 0 ] p , min10) ∷⁺ [ p , per8 ])
  other    : {ps : List⁺ PitchInterval} → (p : PitchInterval) →
             MotionOk (pitchIntervalToInterval p) (pitchIntervalToInterval (head ps)) →
             FirstSpecies ps → FirstSpecies (p ∷⁺ ps)
