{-# OPTIONS --without-K #-}

module Counterpoint where

open import Music hiding (transpose)
open import Note hiding (transpose)
open import Pitch

open import Data.Bool hiding (_≟_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_;  -[1+_])-- hiding (_+_)
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

Interval : Set
Interval = Pitch × Pitch

-- allowed intervals only
data IntervalQuality : Set where
  min3  : IntervalQuality
  maj3  : IntervalQuality
  per5  : IntervalQuality
  min6  : IntervalQuality
  maj6  : IntervalQuality
  per8  : IntervalQuality
  min10 : IntervalQuality
  maj10 : IntervalQuality

PitchInterval : Set
PitchInterval = Pitch × IntervalQuality

pitchIntervalToInterval : PitchInterval → Interval
pitchIntervalToInterval (p , min3)  = p , transpose (+ 3)  p
pitchIntervalToInterval (p , maj3)  = p , transpose (+ 4)  p
pitchIntervalToInterval (p , per5)  = p , transpose (+ 7)  p
pitchIntervalToInterval (p , min6)  = p , transpose (+ 8)  p
pitchIntervalToInterval (p , maj6)  = p , transpose (+ 9)  p
pitchIntervalToInterval (p , per8)  = p , transpose (+ 12) p
pitchIntervalToInterval (p , min10) = p , transpose (+ 15) p
pitchIntervalToInterval (p , maj10) = p , transpose (+ 16) p

isPerfect : IntervalQuality → Bool
isPerfect min3  = false
isPerfect maj3  = false
isPerfect per5  = true
isPerfect min6  = false
isPerfect maj6  = false
isPerfect per8  = true
isPerfect min10 = true
isPerfect maj10 = true

-- assume a ≤ b
isPerfectInterval : Interval → Bool
isPerfectInterval (pitch a , pitch b) =
  let d = b ∸ a
  in if d ≡ᵇ 7 then true else if d ≡ᵇ 12 then true else false

data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

-- assume a ≤ b , c ≤ d
motion : Interval → Interval → Motion
motion (pitch a , pitch b) (pitch c , pitch d) with b ∸ a ≟ d ∸ c | compare a c | compare b d
motion (pitch a , pitch b) (pitch c , pitch d)                           | yes p | y            | z            = parallel
motion (pitch a , pitch b) (pitch .a , pitch d)                          | no ¬p | equal .a     | z            = oblique
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .(suc (b + m))) | no ¬p | less .a k    | less .b m    = similar
motion (pitch a , pitch b) (pitch .(suc (a + k)) , pitch .b)             | no ¬p | less .a k    | equal .b     = oblique
motion (pitch a , pitch .(suc (d + m))) (pitch .(suc (a + k)) , pitch d) | no ¬p | less .a k    | greater .d m = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .(suc (b + m))) | no ¬p | greater .c k | less .b m    = contrary
motion (pitch .(suc (c + k)) , pitch b) (pitch c , pitch .b)             | no ¬p | greater .c k | equal .b     = oblique
motion (pitch .(suc (c + k)) , pitch .(suc (d + m))) (pitch c , pitch d) | no ¬p | greater .c k | greater .d m = similar

motionOk : (i1 : Interval) (i2 : Interval) → Set
motionOk i1 i2 with motion i1 i2 | isPerfectInterval i2
motionOk i1 i2 | contrary | _     = ⊤
motionOk i1 i2 | oblique  | _     = ⊤
motionOk i1 i2 | parallel | false = ⊤
motionOk i1 i2 | parallel | true  = ⊥
motionOk i1 i2 | similar  | false = ⊤
motionOk i1 i2 | similar  | true  = ⊥

-- interval in index is initial interval
-- final interval of a cadence is (p , per 8)
data FirstSpecies : PitchInterval → Set where
  cadence2 : (p : Pitch) → FirstSpecies (transpose (+ 2) p    , maj6)
  cadence7 : (p : Pitch) → FirstSpecies (transpose -[1+ 0 ] p , min10)
  _∷_ : (pi : PitchInterval) → {pj : PitchInterval} →
        {_ : motionOk (pitchIntervalToInterval pi) (pitchIntervalToInterval pj)} →
        FirstSpecies pj → FirstSpecies pi

intervaltoMusic : Interval → Music
intervaltoMusic (p , q) = note (note 8th p) ∥ note (note 8th q)

pitchIntervalToMusic : PitchInterval → Music
pitchIntervalToMusic = intervaltoMusic ∘ pitchIntervalToInterval

firstSpeciesToMusic : {pi : PitchInterval} → FirstSpecies pi → Music
firstSpeciesToMusic {pi} (cadence2 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic {pi} (cadence7 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic      (pi ∷ fs)    = pitchIntervalToMusic pi ∷ firstSpeciesToMusic fs

