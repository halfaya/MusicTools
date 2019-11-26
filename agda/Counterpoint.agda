{-# OPTIONS --without-K #-}

module Counterpoint where

open import Music
open import Note hiding (transpose)
open import Pitch
open import Interval

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _+_;  _∸_; _≟_; compare; equal; less; greater)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using ([]; _∷_)

open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

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
