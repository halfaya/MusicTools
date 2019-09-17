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

Interval : Set
Interval = Pitch × Pitch

-- allowed intervals only
data IntervalQuality : ℕ → Set where
  per1  : IntervalQuality 0
  min2  : IntervalQuality 1
  maj2  : IntervalQuality 2
  min3  : IntervalQuality 3
  maj3  : IntervalQuality 4
  per4  : IntervalQuality 5
  aug4  : IntervalQuality 6
  per5  : IntervalQuality 7
  min6  : IntervalQuality 8
  maj6  : IntervalQuality 9
  min7  : IntervalQuality 10
  maj7  : IntervalQuality 11
  per8  : IntervalQuality 12
  min9  : IntervalQuality 13
  maj9  : IntervalQuality 14
  min10 : IntervalQuality 15
  maj10 : IntervalQuality 16

isConsonant : {n : ℕ} → IntervalQuality n → Bool
isConsonant per1 = true
isConsonant min2 = false
isConsonant maj2 = false
isConsonant min3 = true 
isConsonant maj3 = true
isConsonant per4 = false
isConsonant aug4 = false
isConsonant per5 = true
isConsonant min6 = true
isConsonant maj6 = true
isConsonant min7 = false
isConsonant maj7 = false
isConsonant per8 = true
isConsonant min9 = false
isConsonant maj9 = false
isConsonant min10 = true
isConsonant maj10 = true

isDissonant : {n : ℕ} → IntervalQuality n → Bool
isDissonant = not ∘ isConsonant

PitchInterval : ℕ → Set
PitchInterval n = Pitch × IntervalQuality n

pitchIntervalToInterval : {n : ℕ} → PitchInterval n → Interval
pitchIntervalToInterval {n} (p , _) = (p , transpose (+ n)  p)

isPerfect : {n : ℕ} → IntervalQuality n → Bool
isPerfect per1 = true
isPerfect min2 = false
isPerfect maj2 = false
isPerfect min3 = false
isPerfect maj3 = false
isPerfect per4 = true
isPerfect aug4 = false
isPerfect per5 = true
isPerfect min6 = false
isPerfect maj6 = false
isPerfect min7 = false
isPerfect maj7 = false
isPerfect per8 = true
isPerfect min9 = false
isPerfect maj9 = false
isPerfect min10 = false
isPerfect maj10 = false

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
data FirstSpecies : {n : ℕ} → PitchInterval n → Set where
  cadence2 : (p : Pitch) → FirstSpecies (transpose (+ 2) p    , maj6)
  cadence7 : (p : Pitch) → FirstSpecies (transpose -[1+ 0 ] p , min10)
  _∷_ : {i j : ℕ}(pi : PitchInterval i){_ : (T ∘ isConsonant ∘ proj₂) pi}
        {pj : PitchInterval j}{_ : (T ∘ isConsonant ∘ proj₂) pj} →
        {_ : motionOk (pitchIntervalToInterval pi) (pitchIntervalToInterval pj)} →
        FirstSpecies pj → FirstSpecies pi

intervaltoMusic : Interval → Music
intervaltoMusic (p , q) = note (note 8th p) ∥ note (note 8th q)

pitchIntervalToMusic : {n : ℕ} → PitchInterval n → Music
pitchIntervalToMusic = intervaltoMusic ∘ pitchIntervalToInterval

firstSpeciesToMusic : {n : ℕ}{pi : PitchInterval n} → FirstSpecies pi → Music
firstSpeciesToMusic {n} {pi} (cadence2 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic {n} {pi} (cadence7 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic          (pi ∷ fs)    = pitchIntervalToMusic pi ∷ firstSpeciesToMusic fs
