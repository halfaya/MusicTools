{-# OPTIONS --without-K #-}

module Pitch where

open import Data.Bool       using (Bool; false; true)
open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_)
open import Data.Nat        using (ℕ; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.String     using (String; fromList)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Vec        using (Vec; []; _∷_; map; lookup; replicate; _[_]%=_; toList)
open import Function        using (_∘_)

open import Lemmas          using (revMod; -_mod_; -_div_)
open import Util            using (findIndex)

-- Position of a pitch on an absolute scale
-- 0 is C(-1) on the international scale (where C4 is middle C)
-- or C0 on the Midi scale (where C5 is middle C)
-- Pitch is intentially set to match Midi pitch.
-- However it is fine to let 0 represent some other note and
-- translate appropriately at the end.
data Pitch : Set where
  pitch : ℕ → Pitch

unpitch : Pitch → ℕ
unpitch (pitch p) = p

-- Number of notes in the chromatic scale.
chromaticScaleSize : ℕ
chromaticScaleSize = 12

-- Position of a pitch within an octave, in the range [0..chromaticScaleSize-1].
data PitchClass : Set where
  pitchClass : Fin chromaticScaleSize → PitchClass

Scale : ℕ → Set
Scale = Vec PitchClass

-- Which octave one is in.
data Octave : Set where
  octave : ℕ → Octave

PitchOctave : Set
PitchOctave = PitchClass × Octave

relativeToAbsolute : PitchOctave → Pitch
relativeToAbsolute (pitchClass n , octave o) =
  pitch (o * chromaticScaleSize + (toℕ n))

absoluteToRelative : Pitch → PitchOctave
absoluteToRelative (pitch  n) =
  (pitchClass (n mod chromaticScaleSize) , octave (n div chromaticScaleSize))

pitchToClass : Pitch → PitchClass
pitchToClass = proj₁ ∘ absoluteToRelative

majorScale harmonicMinorScale : Scale 7
majorScale         = map pitchClass (# 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ [])
harmonicMinorScale = map pitchClass (# 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ [])

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

transposePitch : ℤ → Pitch → Pitch
transposePitch (+_     k) (pitch n) = pitch (n + k)
transposePitch (-[1+_] k) (pitch n) = pitch (n ∸ suc k)

-- Set of pitch classes represented as a bit vector.
PitchClassSet : Set
PitchClassSet = Vec Bool chromaticScaleSize

emptyPitchClassSet : PitchClassSet
emptyPitchClassSet = replicate false

addToPitchClassSet : PitchClass → PitchClassSet → PitchClassSet
addToPitchClassSet (pitchClass p) ps = ps [ p ]%= (λ _ → true)

showPitchClassSet : PitchClassSet → String
showPitchClassSet = fromList ∘ toList ∘ map (λ {true → '1' ; false → '0'})

-- Standard Midi pitches

-- first argument is relative pitch within octave
-- second argument is octave (C5 = middle C for Midi)
standardMidiPitch : Fin chromaticScaleSize → ℕ → Pitch
standardMidiPitch p o = relativeToAbsolute (pitchClass p , octave o)

c d e f g g# a b : ℕ → Pitch
c  = standardMidiPitch (# 0)
d  = standardMidiPitch (# 2)
e  = standardMidiPitch (# 4)
f  = standardMidiPitch (# 5)
g  = standardMidiPitch (# 7)
g# = standardMidiPitch (# 8)
a  = standardMidiPitch (# 9)
b  = standardMidiPitch (# 11)

