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

data IntervalQuality : Set where
  fifthOctave : IntervalQuality
  other       : IntervalQuality

-- assume a ≥ b
intervalQuality : Interval → IntervalQuality
intervalQuality (pitch a , pitch b) =
  let d = a ∸ b
  in if d ≡ᵇ 7 then fifthOctave else if d ≡ᵇ 12 then fifthOctave else other

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
  other    : intervalQuality i2 ≡ other → MotionOk i1 i2
  contrary : motion i1 i2 ≡ contrary → MotionOk i1 i2
  oblique  : motion i1 i2 ≡ oblique → MotionOk i1 i2

data FirstSpecies : List⁺ Interval → Set where
  -- p is Cantus Firmus pitch
  cadence2 : (p : Pitch) → FirstSpecies ((transpose (+ 10) p , transpose (+ 2) p)      ∷⁺ [ transpose (+ 12) p , p ])
  cadence7 : (p : Pitch) → FirstSpecies ((transpose (+ 14) p , transpose (-[1+ 1 ]) p) ∷⁺ [ transpose (+ 12) p , p ])
  min3     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 3) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 3) p , p) ∷⁺ ps)
  maj3     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 4) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 4) p , p) ∷⁺ ps)
  per5     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 7) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 7) p , p) ∷⁺ ps)
  min6     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 8) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 8) p , p) ∷⁺ ps)
  maj6     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 9) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 9) p , p) ∷⁺ ps)
  per8     : {ps : List⁺ Interval} → (p : Pitch) → MotionOk (transpose (+ 12) p , p) (head ps) → FirstSpecies ps →
             FirstSpecies ((transpose (+ 12) p , p) ∷⁺ ps)

