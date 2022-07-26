{-# OPTIONS --erased-cubical --safe -W noNoEquivWhenSplitting #-}

module Pitch where

open import Prelude

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert; empty; show)
open import Util            using (n∸k<n; _+N_; opposite)

-- Position of a pitch on an absolute scale
-- 0 is C(-1) on the international scale (where C4 is middle C)
-- or C0 on the Midi scale (where C5 is middle C)
-- Pitch is intentially set to match Midi pitch.
-- However it is fine to let 0 represent some other note and
-- translate appropriately at the end.
Pitch : Type
Pitch = ℕ

-- Number of notes in the chromatic scale.
s12 : ℕ
s12 = 12

-- Number of notes in the diatonic scale.
s7 : ℕ
s7 = 7

-- Pitch Class: position of a pitch within an octave, in the range [0..s12-1].
-- Pitch class 0 corresponds to C (assuming pitch 0 is Midi C0), which is standard.
PC : Type
PC = Fin s12

showPC : PC → String
showPC fz = "0"
showPC (fs fz) = "1"
showPC (fs (fs fz)) = "2"
showPC (fs (fs (fs fz))) = "3"
showPC (fs (fs (fs (fs fz)))) = "4"
showPC (fs (fs (fs (fs (fs fz))))) = "5"
showPC (fs (fs (fs (fs (fs (fs fz)))))) = "6"
showPC (fs (fs (fs (fs (fs (fs (fs fz))))))) = "7"
showPC (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = "8"
showPC (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))) = "9"
showPC (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))) = "a"
showPC (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))) = "b"

showPCs : List PC → String
showPCs pcs = intersperse " " (map showPC pcs)

toPC : Pitch → PC
toPC = _mod s12

Scale : ℕ → Type
Scale = Vec PC

-- Which octave one is in.
Octave : Type
Octave = ℕ

PitchOctave : Type
PitchOctave = PC × Octave

relativeToAbsolute : PitchOctave → Pitch
relativeToAbsolute (n , o) = (o * s12 + (toℕ n))

absoluteToRelative : Pitch → PitchOctave
absoluteToRelative n = (toPC n , n div s12)

pitchToClass : Pitch → PC
pitchToClass = proj₁ ∘ absoluteToRelative

majorScale harmonicMinorScale : Scale s7
majorScale         = # 0 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ []
harmonicMinorScale = # 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 11 ∷ []

wholeTone0Scale wholeTone1Scale : Scale 6
wholeTone0Scale    = # 0 ∷ # 2 ∷ # 4 ∷ # 6 ∷ # 8 ∷ # 10 ∷ []
wholeTone1Scale    = # 1 ∷ # 3 ∷ # 5 ∷ # 7 ∷ # 9 ∷ # 11 ∷ []

octatonic01Scale octatonic02Scale octatonic12Scale : Scale 8
octatonic01Scale   = # 0 ∷ # 1 ∷ # 3 ∷ # 4 ∷ # 6 ∷ # 7 ∷ # 9 ∷ # 10 ∷ []
octatonic02Scale   = # 0 ∷ # 2 ∷ # 3 ∷ # 5 ∷ # 6 ∷ # 8 ∷ # 9 ∷ # 11 ∷ []
octatonic12Scale   = # 1 ∷ # 2 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 8 ∷ # 10 ∷ # 11 ∷ []

majorPentatonicScale minorPentatonicScale ryukyuScale : Scale 5
majorPentatonicScale = # 0 ∷ # 2 ∷ # 4 ∷ # 7 ∷ # 9 ∷ []
minorPentatonicScale = # 0 ∷ # 2 ∷ # 4 ∷ # 7 ∷ # 9 ∷ []
ryukyuScale          = # 0 ∷ # 4 ∷ # 5 ∷ # 7 ∷ # 11 ∷ []

indexInScale : {n : ℕ} → Vec PC n → Fin s12 → Maybe (Fin n)
indexInScale []         p = nothing
indexInScale (pc ∷ pcs) p with pc ≟Fin p
... | yes _ = just fz
... | no  _ = mmap fs (indexInScale pcs p)

scaleSize : {n : ℕ} → Scale n → ℕ
scaleSize {n} _ = n

transposePitch : ℤ → Pitch → Pitch
transposePitch (+_     k) n = n + k
transposePitch (-[1+_] k) n = n ∸ suc k

-- transpose pitch class
Tp : ℕ  → PC → PC
Tp n pc = pc +N n

-- invert pitch class
Ip : PC → PC
Ip = opposite

-- Set of pitch classes represented as a bit vector.
PCSet : Type
PCSet = BitVec s12

toPCSet : List PC → PCSet
toPCSet = foldr insert empty

fromPCSet : PCSet → List PC
fromPCSet pcs = fromPCS s12 pcs
  where fromPCS : (n : ℕ) → BitVec n → List PC
        fromPCS zero []              = []
        fromPCS (suc n) (false ∷ xs) = fromPCS n xs
        fromPCS (suc n) (true  ∷ xs) = fromℕ< (n∸k<n 11 n) ∷ fromPCS n xs

-- transpose pitch class set
T : ℕ → PCSet → PCSet
T n = toPCSet ∘ map (Tp n) ∘ fromPCSet

-- invert pitch class set
I : PCSet → PCSet
I = toPCSet ∘ map Ip ∘ fromPCSet

-- Standard Midi pitches

-- first argument is relative pitch within octave
-- second argument is octave (C5 = middle C for Midi)
standardMidiPitch : Fin s12 → ℕ → Pitch
standardMidiPitch p o = relativeToAbsolute (p , o)

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
  let a = cong pitchClass (modUnique s12 o p)
      b = cong octave     (divUnique s12 o p)
  in a i , b i

abs→rel→abs : (p : Pitch) → (rel→abs ∘ abs→rel) p ≡ p
abs→rel→abs (pitch p) = cong pitch (sym (n≡divmod p s12))

abs≃rel : Iso Pitch PitchOctave
abs≃rel = iso abs→rel rel→abs rel→abs→rel abs→rel→abs

abs≡rel : Pitch ≡ PitchOctave
abs≡rel = isoToPath abs≃rel
-}
