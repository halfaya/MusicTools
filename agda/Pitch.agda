{-# OPTIONS --cubical --safe #-}

module Pitch where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Data.Bool       using (Bool; false; true)
open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Maybe      using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat        using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _>_)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Vec        using (Vec; []; _∷_; map; lookup; replicate; _[_]%=_; toList)

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert)
open import DivMod          using (_mod_; _div_; DivMod; n≡divmod {-; divUnique; modUnique -})

-- Position of a pitch on an absolute scale
-- 0 is C(-1) on the international scale (where C4 is middle C)
-- or C0 on the Midi scale (where C5 is middle C)
-- Pitch is intentially set to match Midi pitch.
-- However it is fine to let 0 represent some other note and
-- translate appropriately at the end.
data Pitch : Type where
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
data PitchClass : Type where
  pitchClass : Fin chromaticScaleSize → PitchClass

unPitchClass : PitchClass → Fin chromaticScaleSize
unPitchClass (pitchClass p) = p

Scale : ℕ → Type
Scale = Vec PitchClass

-- Which octave one is in.
data Octave : Type where
  octave : ℕ → Octave

unoctave : Octave → ℕ
unoctave (octave n) = n

PitchOctave : Type
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

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

transposePitch : ℤ → Pitch → Pitch
transposePitch (+_     k) (pitch n) = pitch (n + k)
transposePitch (-[1+_] k) (pitch n) = pitch (n ∸ suc k)

-- Set of pitch classes represented as a bit vector.
PitchClassSet : Type
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

-- Equivalences

rel→abs : PitchOctave → Pitch
rel→abs = relativeToAbsolute

abs→rel : Pitch → PitchOctave
abs→rel = absoluteToRelative

{-
rel→abs→rel : (p : PitchOctave) → (abs→rel ∘ rel→abs) p ≡ p
rel→abs→rel (pitchClass p , octave o) i =
  let a = cong pitchClass (modUnique chromaticScaleSize o p)
      b = cong octave     (divUnique chromaticScaleSize o p)
  in a i , b i
-}

abs→rel→abs : (p : Pitch) → (rel→abs ∘ abs→rel) p ≡ p
abs→rel→abs (pitch p) = cong pitch (sym (n≡divmod p chromaticScaleSize))

{-
abs≃rel : Iso Pitch PitchOctave
abs≃rel = iso abs→rel rel→abs rel→abs→rel abs→rel→abs

abs≡rel : Pitch ≡ PitchOctave
abs≡rel = isoToPath abs≃rel
-}
