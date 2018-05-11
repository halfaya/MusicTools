module Pitch where

open import Data.Fin renaming (_+_ to _Fin+_; _-_ to _Fin-_)
open import Data.Integer
open import Data.Vec
open import Data.Nat renaming (_+_ to _N+_;  _*_ to _N*_)
open import Data.Nat.DivMod
open import Data.Product renaming (map to pmap)
open import Function using (_∘_)

open import Lemmas

-- Position of a pitch on an absolute scale; 0 is later mapped to a base frequency.
data Pitch : Set where
  pitch : ℤ → Pitch

getPitch : Pitch → ℤ
getPitch (pitch p) = p

-- Number of steps in the scale (in this case chromatic).
-- Currently this must be 12.
chromaticScaleSize : ℕ
chromaticScaleSize = 12

-- Position of a pitch within an octave, in the range [0..chromaticScaleSize-1].
data RelativePitch : Set where
  relativePitch : Fin chromaticScaleSize → RelativePitch

Scale = Vec RelativePitch

-- Which octave one is in.
data Octave : Set where
  octave : ℤ → Octave

PitchOctave = RelativePitch × Octave

relativeToAbsolute : PitchOctave → Pitch
relativeToAbsolute (relativePitch n , octave o) =
  pitch (o * (+ chromaticScaleSize) + (+ (toℕ (toℕ n mod chromaticScaleSize))))

absoluteToRelative : Pitch → PitchOctave
absoluteToRelative (pitch (+    n  )) =
  (relativePitch (n mod chromaticScaleSize) , octave (+ (n div chromaticScaleSize)))
absoluteToRelative (pitch (-[1+ n ])) =
  (relativePitch (revMod (n mod chromaticScaleSize)) ,
   octave (-[1+ (n div chromaticScaleSize)]))

majorScale harmonicMinorScale : Scale 7
majorScale         = map relativePitch (# 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ [])
harmonicMinorScale = map relativePitch (# 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ [])

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

data ScaleDegree (n : ℕ) : Set where
  scaleDegree : Fin n → ScaleDegree n

ScaleDegreeOctave : ℕ → Set
ScaleDegreeOctave = λ n → ScaleDegree n × Octave

scaleDegreeToRelativePitch : {n : ℕ} → Scale n → ScaleDegree n → RelativePitch
scaleDegreeToRelativePitch scale (scaleDegree d) = lookup d scale

addToScalePitch : {n : ℕ} → ℤ → ScaleDegreeOctave (ℕ.suc n) → ScaleDegreeOctave (ℕ.suc n)
addToScalePitch {n} (+_     k) (scaleDegree d , octave o) =
  let d' = (toℕ d) N+ k
  in scaleDegree (d' mod (ℕ.suc n)) , octave (o + (+ (d' div (ℕ.suc n))))
addToScalePitch {n} (-[1+_] k) (scaleDegree d , octave o) =
  let d' = (toℕ d) N+ k
  in scaleDegree (d' mod (ℕ.suc n)) , octave (o + (+ (d' div (ℕ.suc n)))) -- TODO: Fix

transpose : ℤ → Pitch → Pitch
transpose k (pitch n) = pitch (n + k)

----

-- Standard Midi pitches

c d e f g a b : ℕ → Pitch
c n = pitch ((+ 0)  + ((+ 12) * ((+ n) - (+ 3))))
d n = pitch ((+ 2)  + ((+ 12) * ((+ n) - (+ 3))))
e n = pitch ((+ 4)  + ((+ 12) * ((+ n) - (+ 3))))
f n = pitch ((+ 5)  + ((+ 12) * ((+ n) - (+ 3))))
g n = pitch ((+ 7)  + ((+ 12) * ((+ n) - (+ 3))))
a n = pitch ((+ 9)  + ((+ 12) * ((+ n) - (+ 3))))
b n = pitch ((+ 11) + ((+ 12) * ((+ n) - (+ 3))))

