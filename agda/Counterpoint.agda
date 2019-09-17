{-# OPTIONS --without-K #-}

module Counterpoint where

open import Music hiding (transpose)
open import Note hiding (transpose)
open import Pitch

open import Data.Bool hiding (_≟_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_;  -[1+_])
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

PitchPair : Set
PitchPair = Pitch × Pitch

data Interval : Set where
  interval : ℕ → Interval

_=i_ : Interval → Interval → Bool
(interval a) =i (interval b) = a ≡ᵇ b

infix 4 _=i_

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

-- TODO: Generalize
isConsonant : Interval → Bool
isConsonant i =
  (i =i per1)  ∨
  (i =i min3)  ∨
  (i =i maj3)  ∨
  (i =i per5)  ∨
  (i =i min6)  ∨
  (i =i maj6)  ∨
  (i =i per8)  ∨
  (i =i min10) ∨
  (i =i maj10)

isDissonant : Interval → Bool
isDissonant = not ∘ isConsonant

PitchInterval : Set
PitchInterval = Pitch × Interval

pitchIntervalToPitchPair : PitchInterval → PitchPair
pitchIntervalToPitchPair (p , interval n) = (p , transpose (+ n)  p)

-- assume a ≤ b
pitchPairInterval : PitchPair → Interval
pitchPairInterval (pitch a , pitch b) = interval (b ∸ a)

-- TODO: Generalize
isPerfect : Interval → Bool
isPerfect i =
  (i =i per1)  ∨
  (i =i per4)  ∨
  (i =i per5)  ∨
  (i =i per8)

-- assume a ≤ b
isPerfectPair : PitchPair → Bool
isPerfectPair = isPerfect ∘ pitchPairInterval

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

motionOk : (i1 : PitchPair) (i2 : PitchPair) → Set
motionOk i1 i2 with motion i1 i2 | isPerfectPair i2
motionOk i1 i2 | contrary | _     = ⊤
motionOk i1 i2 | oblique  | _     = ⊤
motionOk i1 i2 | parallel | false = ⊤
motionOk i1 i2 | parallel | true  = ⊥
motionOk i1 i2 | similar  | false = ⊤
motionOk i1 i2 | similar  | true  = ⊥

-- interval in index is initial interval
-- final interval of a cadence is (p , per 8)
data FirstSpecies :  PitchInterval → Set where
  cadence2 : (p : Pitch) → FirstSpecies (transpose (+ 2) p    , maj6)
  cadence7 : (p : Pitch) → FirstSpecies (transpose -[1+ 0 ] p , min10)
  _∷_ : (pi : PitchInterval){_ : (T ∘ isConsonant ∘ proj₂) pi}
        {pj : PitchInterval}{_ : (T ∘ isConsonant ∘ proj₂) pj} →
        {_ : motionOk (pitchIntervalToPitchPair pi) (pitchIntervalToPitchPair pj)} →
        FirstSpecies pj → FirstSpecies pi

intervaltoMusic : PitchPair → Music
intervaltoMusic (p , q) = note (note 8th p) ∥ note (note 8th q)

pitchIntervalToMusic :  PitchInterval → Music
pitchIntervalToMusic = intervaltoMusic ∘ pitchIntervalToPitchPair

firstSpeciesToMusic : {pi : PitchInterval} → FirstSpecies pi → Music
firstSpeciesToMusic {pi} (cadence2 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic {pi} (cadence7 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic      (pi ∷ fs)    = pitchIntervalToMusic pi ∷ firstSpeciesToMusic fs
