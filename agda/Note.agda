module Note where

open import Data.Fin renaming (_+_ to _Fin+_)
open import Data.Integer
open import Data.Vec
open import Data.Nat renaming (_+_ to _N+_;  _*_ to _N*_)
open import Data.Nat.DivMod
open import Data.Product renaming (map to pmap)
open import Function

-- Position of a note on an absolute scale; 0 is later mapped to a base frequency.
data Note : Set where
  note : ℤ → Note

-- Number of steps in the scale (in this case chromatic).
-- Currently this must be 12.
chromaticScaleSize : ℕ
chromaticScaleSize = 12

-- Position of a note within an octave, in the range [0..chromaticScaleSize-1].
data RelativeNote : Set where
  relativeNote : Fin chromaticScaleSize → RelativeNote

Scale = Vec RelativeNote

-- Which octave one is in.
data Octave : Set where
  octave : ℤ → Octave

NoteOctave = RelativeNote × Octave

relativeToAbsolute : NoteOctave → Note
relativeToAbsolute (relativeNote n , octave o) =
  note (o * (+ chromaticScaleSize) + (+ (toℕ (toℕ n mod chromaticScaleSize))))

absoluteToRelative : Note → NoteOctave
absoluteToRelative (note (+    n  )) =
  (relativeNote (n mod chromaticScaleSize) , octave (+ (n div chromaticScaleSize)))
absoluteToRelative (note (-[1+ n ])) =
  (relativeNote (n mod chromaticScaleSize) , octave (+ (n div chromaticScaleSize))) -- TODO: Fix

majorScale harmonicMinorScale : Scale 7
majorScale         = map relativeNote (# 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ [])
harmonicMinorScale = map relativeNote (# 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ [])

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

data ScaleDegree (n : ℕ) : Set where
  scaleDegree : Fin n → ScaleDegree n

ScaleDegreeOctave = λ n → ScaleDegree n × Octave

scaleDegreeToRelativeNote : {n : ℕ} → Scale n → ScaleDegree n → RelativeNote
scaleDegreeToRelativeNote scale (scaleDegree d) = lookup d scale

addToScaleNote : {n : ℕ} → ℤ → ScaleDegreeOctave (ℕ.suc n) → ScaleDegreeOctave (ℕ.suc n)
addToScaleNote {n} (+_     k) (scaleDegree d , octave o) =
  let d' = (toℕ d) N+ k
  in scaleDegree (d' mod (ℕ.suc n)) , octave (o + (+ (d' div (ℕ.suc n))))
addToScaleNote {n} (-[1+_] k) (scaleDegree d , octave o) =
  let d' = (toℕ d) N+ k
  in scaleDegree (d' mod (ℕ.suc n)) , octave (o + (+ (d' div (ℕ.suc n)))) -- TODO: Fix

transpose : ℤ → Note → Note
transpose k (note n) = note (n + k)
