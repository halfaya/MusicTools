{-# OPTIONS --without-K #-}

module Pitch where

open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_)
open import Data.Vec        using (Vec; []; _∷_; map; lookup)
open import Data.Nat        using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_)
open import Function        using (_∘_)

open import Lemmas          using (revMod; -_mod_; -_div_)
open import Util            using (findIndex)

-- Position of a pitch on an absolute scale
-- 0 is C(-1) on the international scale (where C4 is middle C)
-- or C0 on the Midi scale (where C5 is middle C)
-- Pitch is intentially set to match Midi pitch.
data Pitch : Set where
  pitch : ℕ → Pitch

pitchValue : Pitch → ℕ
pitchValue (pitch p) = p

-- Number of steps in the scale (in this case chromatic).
-- Currently this must be 12.
chromaticScaleSize : ℕ
chromaticScaleSize = 12

-- Position of a pitch within an octave, in the range [0..chromaticScaleSize-1].
data RelativePitch : Set where
  relativePitch : Fin chromaticScaleSize → RelativePitch

Scale : ℕ → Set
Scale = Vec RelativePitch

-- Which octave one is in.
data Octave : Set where
  octave : ℕ → Octave

PitchOctave : Set
PitchOctave = RelativePitch × Octave

relativeToAbsolute : PitchOctave → Pitch
relativeToAbsolute (relativePitch n , octave o) =
  pitch (o * chromaticScaleSize + (toℕ n))

absoluteToRelative : Pitch → PitchOctave
absoluteToRelative (pitch  n) =
  (relativePitch (n mod chromaticScaleSize) , octave (n div chromaticScaleSize))

majorScale harmonicMinorScale : Scale 7
majorScale         = map relativePitch (# 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ [])
harmonicMinorScale = map relativePitch (# 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ [])

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

transpose : ℤ → Pitch → Pitch
transpose (+_     k) (pitch n) = pitch (n + k)
transpose (-[1+_] k) (pitch n) = pitch (n ∸ suc k)

----

-- Standard Midi pitches

-- first argument is relative pitch within octave
-- second argument is octave (C5 = middle C for Midi)
standardMidiPitch : Fin chromaticScaleSize → ℕ → Pitch
standardMidiPitch p o = relativeToAbsolute (relativePitch p , octave o)

c d e f g g# a b : ℕ → Pitch
c  = standardMidiPitch (# 0)
d  = standardMidiPitch (# 2)
e  = standardMidiPitch (# 4)
f  = standardMidiPitch (# 5)
g  = standardMidiPitch (# 7)
g# = standardMidiPitch (# 8)
a  = standardMidiPitch (# 9)
b  = standardMidiPitch (# 11)

