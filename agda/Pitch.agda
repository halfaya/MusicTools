{-# OPTIONS --without-K #-}

module Pitch where

open import Data.Bool       using (Bool; false; true)
open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Maybe      using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat        using (ℕ; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Vec        using (Vec; []; _∷_; map; lookup; replicate; _[_]%=_; toList)
open import Function        using (_∘_)

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert)
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

-- Number of notes in the diatonic scale.
diatonicScaleSize : ℕ
diatonicScaleSize = 7

-- Position of a pitch within an octave, in the range [0..chromaticScaleSize-1].
data PitchClass : Set where
  pitchClass : Fin chromaticScaleSize → PitchClass

unPitchClass : PitchClass → Fin chromaticScaleSize
unPitchClass (pitchClass p) = p

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

majorScale harmonicMinorScale : Scale diatonicScaleSize
majorScale         = map pitchClass (# 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ [])
harmonicMinorScale = map pitchClass (# 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ [])

indexInScale : {n : ℕ} → Vec PitchClass n → Fin chromaticScaleSize → Maybe (Fin n)
indexInScale []         p = nothing
indexInScale (pc ∷ pcs) p with (unPitchClass pc ≟ p)
... | yes _ = just fz
... | no  _ = mmap fs (indexInScale pcs p)

data DiatonicDegree : Set where
  diatonicDegree : Fin diatonicScaleSize → DiatonicDegree

undd : DiatonicDegree → Fin diatonicScaleSize
undd (diatonicDegree d) = d

infix 4 _≡ᵈ_
_≡ᵈ_ : DiatonicDegree → DiatonicDegree → Bool
diatonicDegree d ≡ᵈ diatonicDegree e = toℕ d ≡ᵇ toℕ e

-- round down
pitchClassToDegreeMajor : PitchClass → DiatonicDegree
pitchClassToDegreeMajor (pitchClass fz)                                                        = diatonicDegree (# 0)
pitchClassToDegreeMajor (pitchClass (fs fz))                                                   = diatonicDegree (# 0)
pitchClassToDegreeMajor (pitchClass (fs (fs fz)))                                              = diatonicDegree (# 1)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs fz))))                                         = diatonicDegree (# 1)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs fz)))))                                    = diatonicDegree (# 2)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs fz))))))                               = diatonicDegree (# 3)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs fz)))))))                          = diatonicDegree (# 3)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs (fs fz))))))))                     = diatonicDegree (# 4)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))                = diatonicDegree (# 4)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))           = diatonicDegree (# 5)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))      = diatonicDegree (# 5)
pitchClassToDegreeMajor (pitchClass (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))) = diatonicDegree (# 6)

pitchToDegreeCMajor : Pitch → DiatonicDegree
pitchToDegreeCMajor = pitchClassToDegreeMajor ∘ pitchToClass

d1 d2 d3 d4 d5 d6 d7 : DiatonicDegree
d1 = diatonicDegree (# 0)
d2 = diatonicDegree (# 1)
d3 = diatonicDegree (# 2)
d4 = diatonicDegree (# 3)
d5 = diatonicDegree (# 4)
d6 = diatonicDegree (# 5)
d7 = diatonicDegree (# 6)

thirdUp : DiatonicDegree → DiatonicDegree
thirdUp (diatonicDegree d) = diatonicDegree ((toℕ d + 2) mod diatonicScaleSize)

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

transposePitch : ℤ → Pitch → Pitch
transposePitch (+_     k) (pitch n) = pitch (n + k)
transposePitch (-[1+_] k) (pitch n) = pitch (n ∸ suc k)

-- Set of pitch classes represented as a bit vector.
PitchClassSet : Set
PitchClassSet = BitVec chromaticScaleSize

addToPitchClassSet : PitchClass → PitchClassSet → PitchClassSet
addToPitchClassSet (pitchClass p) ps = insert p ps

-- Standard Midi pitches

-- first argument is relative pitch within octave
-- second argument is octave (C5 = middle C for Midi)
standardMidiPitch : Fin chromaticScaleSize → ℕ → Pitch
standardMidiPitch p o = relativeToAbsolute (pitchClass p , octave o)

c c♯ d d♯ e f f♯ g g♯ a b♭ b : ℕ → Pitch
c  = standardMidiPitch (# 0)
c♯ = standardMidiPitch (# 1)
d  = standardMidiPitch (# 2)
d♯ = standardMidiPitch (# 3)
e  = standardMidiPitch (# 4)
f  = standardMidiPitch (# 5)
f♯ = standardMidiPitch (# 6)
g  = standardMidiPitch (# 7)
g♯ = standardMidiPitch (# 8)
a  = standardMidiPitch (# 9)
b♭ = standardMidiPitch (# 10)
b  = standardMidiPitch (# 11)
