{-# OPTIONS --without-K --safe #-}

module Symbolic where

open import Prelude

open import Expr hiding (_+_; #_; lookup; _mod_)
open import Pitch
open import Interval
open import Location

data Letter : Type where
  C : Letter
  D : Letter
  E : Letter
  F : Letter
  G : Letter
  A : Letter
  B : Letter

showLetter : Letter → String
showLetter C = "C"
showLetter D = "D"
showLetter E = "E"
showLetter F = "F"
showLetter G = "G"
showLetter A = "A"
showLetter B = "B"

-- Accidentals
data Acc : Type where
  ♮ : Acc
  ♭ : Acc
  ♯ : Acc
  𝄫 : Acc
  𝄪 : Acc

showAcc : Acc → String
showAcc ♮ = ""
showAcc ♭ = "♭"
showAcc ♯ = "♯"
showAcc 𝄫 = "𝄫"
showAcc 𝄪 = "𝄪"

record NoteName : Type where
  constructor nn
  field
    ltr : Letter
    acc : Acc

-- Specific notes
C♮ = nn C ♮
C♯ = nn C ♯
D♭ = nn D ♭
D♮ = nn D ♮
D♯ = nn D ♯
E♭ = nn E ♭
E♮ = nn E ♮
F♮ = nn F ♮
F♯ = nn F ♯
G♭ = nn G ♭
G♮ = nn G ♮
G♯ = nn G ♯
A♭ = nn A ♭
A♮ = nn A ♮
A♯ = nn A ♯
B♭ = nn B ♭
B♮ = nn B ♮

showNoteName : NoteName → String
showNoteName (nn l a) = showLetter l ++s showAcc a

letter→PC : Letter → PC
letter→PC C = # 0
letter→PC D = # 2
letter→PC E = # 4
letter→PC F = # 5
letter→PC G = # 7
letter→PC A = # 9
letter→PC B = # 11

-- Actual modifier is this value minus 2.
acc→mod : Acc → ℕ
acc→mod ♮ = 2
acc→mod ♭ = 1
acc→mod ♯ = 3
acc→mod 𝄫 = 0
acc→mod 𝄪 = 4

noteName→PC : NoteName → PC
noteName→PC (nn l a) = (toℕ (letter→PC l) + acc→mod a + 10) mod s12

-- Named Pitch
record NPitch : Type where
  constructor np
  field
    nam : NoteName
    oct : Octave

showNPitch : NPitch → String
showNPitch (np n o) = showNoteName n ++s primShowNat o

-- Maybe named pitch; the alternative is a variable with a unique name
data MPitch : Type where
  !! : NPitch → MPitch
  ?? : String → MPitch

showMPitch : MPitch → String
showMPitch (!! x) = showNPitch x
showMPitch (?? s) = "?" ++s s

-- Note: This doesn't work for C♭, etc, with values < 0.
np→pitch : NPitch → IExpr
np→pitch (np n o) = N (o * s12 + toℕ (noteName→PC n))

name→pitch : MPitch → IExpr
name→pitch (!! n) = np→pitch n
name→pitch (?? s) = var s

name→pitch2 : MPitch × MPitch → IExpr × IExpr
name→pitch2 (a , b ) = name→pitch a , name→pitch b

-- Map unknown pitches to 0 for now.
name→p : Dict → MPitch → Pitch
name→p d (!! namp) with evalI d (np→pitch namp)
... | +_     n = n
... | -[1+_] _ = 0
name→p _ (?? _) = 0

-- Named Interval
data NInt : Type where
  Per1  : NInt
  Min2  : NInt
  Maj2  : NInt
  Min3  : NInt
  Maj3  : NInt
  Per4  : NInt
  Aug4  : NInt
  Per5  : NInt
  Min6  : NInt
  Maj6  : NInt
  Min7  : NInt
  Maj7  : NInt
  Per8  : NInt
  Min9  : NInt
  Maj9  : NInt
  Min10 : NInt
  Maj10 : NInt
  Per11 : NInt
  Aug11 : NInt
  Per12 : NInt
  Min13 : NInt
  Maj13 : NInt
  Min14 : NInt
  Maj14 : NInt
  Per15 : NInt
  Int   : Upi → NInt

showNInt : NInt → String
showNInt Per1    = "Per1"
showNInt Min2    = "Min2"
showNInt Maj2    = "Maj2"
showNInt Min3    = "Min3"
showNInt Maj3    = "Maj3"
showNInt Per4    = "Per4"
showNInt Aug4    = "Aug4"
showNInt Per5    = "Per5"
showNInt Min6    = "Min6"
showNInt Maj6    = "Maj6"
showNInt Min7    = "Min7"
showNInt Maj7    = "Maj7"
showNInt Per8    = "Per8"
showNInt Min9    = "Min9"
showNInt Maj9    = "Maj9"
showNInt Min10   = "Min10"
showNInt Maj10   = "Maj10"
showNInt Per11   = "Per11"
showNInt Aug11   = "Aug11"
showNInt Per12   = "Per12"
showNInt Min13   = "Min13"
showNInt Maj13   = "Maj13"
showNInt Min14   = "Min14"
showNInt Maj14   = "Maj14"
showNInt Per15   = "Per15"
showNInt (Int n) = "Int" ++s primShowNat n

name→upi : NInt → Upi
name→upi Per1    = per1
name→upi Min2    = min2
name→upi Maj2    = maj2
name→upi Min3    = min3
name→upi Maj3    = maj3
name→upi Per4    = per4
name→upi Aug4    = aug4
name→upi Per5    = per5
name→upi Min6    = min6
name→upi Maj6    = maj6
name→upi Min7    = min7
name→upi Maj7    = maj7
name→upi Per8    = per8
name→upi Min9    = min9
name→upi Maj9    = maj9
name→upi Min10   = min10
name→upi Maj10   = maj10
name→upi Per11   = per11
name→upi Aug11   = aug11
name→upi Per12   = per12
name→upi Min13   = min13
name→upi Maj13   = maj13
name→upi Min14   = min14
name→upi Maj14   = maj14
name→upi Per15   = per15
name→upi (Int n) = n

upi→name : Upi → NInt
upi→name zero = Per1
upi→name (suc zero) = Min2
upi→name (suc (suc zero)) = Maj2
upi→name (suc (suc (suc zero))) = Min3
upi→name (suc (suc (suc (suc zero)))) = Maj3
upi→name (suc (suc (suc (suc (suc zero))))) = Per4
upi→name (suc (suc (suc (suc (suc (suc zero)))))) = Aug4
upi→name (suc (suc (suc (suc (suc (suc (suc zero))))))) = Per5
upi→name (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Min6
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = Maj6
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = Min7
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = Maj7
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = Per8
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = Min9
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = Maj9
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = Min10
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))) = Maj10
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))) = Per11
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))) = Aug11
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))) = Per12
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))) = Min13
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) = Maj13
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) = Min14
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) = Maj14
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) = Per15
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) = Int (25 + n)

nint : Dict → MPitch → MPitch → NInt
nint d a b = upi→name (upi (name→p d a) (name→p d b))

-- Keys (just a few for now)
data KeyRoot : Type where
  C : KeyRoot
  F : KeyRoot
  G : KeyRoot

showKeyRoot : KeyRoot → String
showKeyRoot C = "C"
showKeyRoot F = "F"
showKeyRoot G = "G"

data KeyQuality : Type where
  major         : KeyQuality
--  naturalMinor  : KeyQuality
--  harmonicMinor : KeyQuality
--  melodicMinor  : KeyQuality

showKeyQuality : KeyQuality → String
showKeyQuality major = "maj"

-- For now these are 7 note scales
data Key : Type where
  key : KeyRoot → KeyQuality → Key

showKey : Key → String
showKey (key k q) = showKeyRoot k ++s showKeyQuality q

scale : Key → Vec NoteName s7
scale (key C major) = C♮ ∷ D♮ ∷ E♮ ∷ F♮ ∷ G♮ ∷ A♮ ∷ B♮ ∷ []
scale (key F major) = F♮ ∷ G♮ ∷ A♮ ∷ B♭ ∷ C♮ ∷ D♮ ∷ E♮ ∷ []
scale (key G major) = G♮ ∷ A♮ ∷ B♮ ∷ C♮ ∷ D♮ ∷ E♮ ∷ F♯ ∷ []

chromaticScale : Vec NoteName s12
chromaticScale = C♮ ∷ C♯ ∷ D♮ ∷ E♭ ∷ E♮ ∷ F♮ ∷ F♯ ∷ G♮ ∷ A♭ ∷ A♮ ∷ B♭ ∷ B♮ ∷ []

toScale : {n : ℕ} → Vec NoteName n → Scale n
toScale = vmap noteName→PC

pitch→npitch : Pitch → NPitch
pitch→npitch n =
  let (p , o) = absoluteToRelative n
  in np (lookup chromaticScale p) o

-- Pairs and pairs of pairs of MPitch
NP NPNP LP LPLP [N] [[N]] [L] [[L]] : Type
NP    = MPitch × MPitch
NPNP  = NP × NP
LP    = Located MPitch × Located MPitch
LPLP  = LP × LP
[N]   = List MPitch
[[N]] = List [N]
[L]   = List (Located MPitch)
[[L]] = List [L]

np→p : NP → P
np→p (a , b) = name→pitch a , name→pitch b

npnp→pp : NPNP → PP
npnp→pp (a , b) = np→p a , np→p b

[n]→[p] : [N] → [P]
[n]→[p] = map name→pitch

[[n]]→[[p]] : [[N]] → [[P]]
[[n]]→[[p]] = map [n]→[p]

lp→np : LP → NP
lp→np (located _ a , located _ b) = a , b

lplp→npnp : LPLP → NPNP
lplp→npnp (a , b) = lp→np a , lp→np b

[l]→[p] : [L] → [P]
[l]→[p] = map (name→pitch ∘ unlocate)

[[l]]→[[p]] : [[L]] → [[P]]
[[l]]→[[p]] = map [l]→[p]

-- Assumes higher voice is first; range starts with higher voice
lpRange : LP → Range
lpRange (located l1 _ , located l2 _) = rectangle l1 l2

-- Assumes higher voice is first; range starts with higher voice
lplpRange : LPLP → Range
lplpRange ((located l1 _ , located l2 _) , (located l3 _ , located l4 _)) = rectangle l1 l4
