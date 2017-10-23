module Note where

open import Data.Fin renaming (_+_ to _Fin+_)
open import Function
open import Data.Integer
open import Data.List renaming (map to lmap)
open import Data.Vec
open import Data.Nat renaming (_+_ to _N+_;  _*_ to _N*_)
open import Data.Nat.DivMod
open import Data.Product renaming (map to pmap)

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

{-
-- TODO: Check that this works with negative k.
addToScaleNote : Int → Int → ScaleDegreeOctave → ScaleDegreeOctave
addToScaleNote scaleSize k (ScaleDegree d, Octave o) =
  (ScaleDegree $ (d + k) `mod` scaleSize, Octave $ o + (d + k) `div` scaleSize)
-}

transpose : ℤ → Note → Note
transpose k (note n) = note (n + k)
