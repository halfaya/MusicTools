{-# OPTIONS --without-K --safe #-}

module Symbolic where

open import Prelude

open import Expr hiding (_+_; #_; _mod_) renaming (lookup to lookupE)
open import Note using (Duration)
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
  𝄫 : Acc
  ♭ : Acc
  ♮ : Acc
  ♯ : Acc
  𝄪 : Acc

showAcc : Acc → String
showAcc 𝄫 = "𝄫"
showAcc ♭ = "♭"
showAcc ♮ = ""
showAcc ♯ = "♯"
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
acc→mod 𝄫 = 0
acc→mod ♭ = 1
acc→mod ♮ = 2
acc→mod ♯ = 3
acc→mod 𝄪 = 4

noteName→PC : NoteName → PC
noteName→PC (nn l a) = (toℕ (letter→PC l) + acc→mod a + 10) mod s12

-- Symbolic Pitch
record SPitch : Type where
  constructor sp
  field
    nam : NoteName
    oct : Octave

showSPitch : SPitch → String
showSPitch (sp n o) = showNoteName n ++s showℕ o

-- Maybe named pitch; the alternative is a variable with a unique name
data MPitch : Type where
  !! : SPitch → MPitch
  ?? : String → MPitch

showMPitch : MPitch → String
showMPitch (!! x) = showSPitch x
showMPitch (?? s) = "?" ++s s

-- Note: This doesn't work for C♭, etc, with values < 0.
np→pitch : SPitch → Pitch
np→pitch (sp n o) = relativeToAbsolute (noteName→PC n , o)

np→iexpr : SPitch → IExpr
np→iexpr n = N (np→pitch n)

-- Map unknown pitches to 0 for now.
mp→pitch : Dict → MPitch → Pitch
mp→pitch d (!! n) = np→pitch n
mp→pitch d (?? s) with lookupE d s
... | +_ p     = p
... | -[1+_] p = 0

name→iexpr : MPitch → IExpr
name→iexpr (!! n) = np→iexpr n
name→iexpr (?? s) = var s

name→iexpr2 : MPitch × MPitch → IExpr × IExpr
name→iexpr2 (a , b ) = name→iexpr a , name→iexpr b

-- Symbolic Note
record SNote : Type where
  constructor sn
  field
    pit : MPitch
    dur : Duration

showSNote : SNote → String
showSNote (sn p d) = showMPitch p ++s showℕ d

-- Symbolic Interval
data SInt : Type where
  Per1  : SInt
  Min2  : SInt
  Maj2  : SInt
  Min3  : SInt
  Maj3  : SInt
  Per4  : SInt
  Aug4  : SInt
  Per5  : SInt
  Min6  : SInt
  Maj6  : SInt
  Min7  : SInt
  Maj7  : SInt
  Per8  : SInt
  Min9  : SInt
  Maj9  : SInt
  Min10 : SInt
  Maj10 : SInt
  Per11 : SInt
  Aug11 : SInt
  Per12 : SInt
  Min13 : SInt
  Maj13 : SInt
  Min14 : SInt
  Maj14 : SInt
  Per15 : SInt
  Int   : Upi → SInt

showSInt : SInt → String
showSInt Per1    = "Per1"
showSInt Min2    = "Min2"
showSInt Maj2    = "Maj2"
showSInt Min3    = "Min3"
showSInt Maj3    = "Maj3"
showSInt Per4    = "Per4"
showSInt Aug4    = "Aug4"
showSInt Per5    = "Per5"
showSInt Min6    = "Min6"
showSInt Maj6    = "Maj6"
showSInt Min7    = "Min7"
showSInt Maj7    = "Maj7"
showSInt Per8    = "Per8"
showSInt Min9    = "Min9"
showSInt Maj9    = "Maj9"
showSInt Min10   = "Min10"
showSInt Maj10   = "Maj10"
showSInt Per11   = "Per11"
showSInt Aug11   = "Aug11"
showSInt Per12   = "Per12"
showSInt Min13   = "Min13"
showSInt Maj13   = "Maj13"
showSInt Min14   = "Min14"
showSInt Maj14   = "Maj14"
showSInt Per15   = "Per15"
showSInt (Int n) = "Int" ++s showℕ n

sint→upi : SInt → Upi
sint→upi Per1    = per1
sint→upi Min2    = min2
sint→upi Maj2    = maj2
sint→upi Min3    = min3
sint→upi Maj3    = maj3
sint→upi Per4    = per4
sint→upi Aug4    = aug4
sint→upi Per5    = per5
sint→upi Min6    = min6
sint→upi Maj6    = maj6
sint→upi Min7    = min7
sint→upi Maj7    = maj7
sint→upi Per8    = per8
sint→upi Min9    = min9
sint→upi Maj9    = maj9
sint→upi Min10   = min10
sint→upi Maj10   = maj10
sint→upi Per11   = per11
sint→upi Aug11   = aug11
sint→upi Per12   = per12
sint→upi Min13   = min13
sint→upi Maj13   = maj13
sint→upi Min14   = min14
sint→upi Maj14   = maj14
sint→upi Per15   = per15
sint→upi (Int n) = n

upi→sint : Upi → SInt
upi→sint zero = Per1
upi→sint (suc zero) = Min2
upi→sint (suc (suc zero)) = Maj2
upi→sint (suc (suc (suc zero))) = Min3
upi→sint (suc (suc (suc (suc zero)))) = Maj3
upi→sint (suc (suc (suc (suc (suc zero))))) = Per4
upi→sint (suc (suc (suc (suc (suc (suc zero)))))) = Aug4
upi→sint (suc (suc (suc (suc (suc (suc (suc zero))))))) = Per5
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Min6
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = Maj6
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = Min7
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = Maj7
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = Per8
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = Min9
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = Maj9
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = Min10
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))) = Maj10
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))) = Per11
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))) = Aug11
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))) = Per12
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))) = Min13
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) = Maj13
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) = Min14
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) = Maj14
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) = Per15
upi→sint (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) = Int (25 + n)

sint : Dict → MPitch → MPitch → SInt
sint d a b = upi→sint (upi (mp→pitch d a) (mp→pitch d b))

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

pitch→np : Pitch → SPitch
pitch→np n =
  let (p , o) = absoluteToRelative n
  in sp (lookup chromaticScale p) o

-- Map unknown pitches to C♮0 for now.
mp→np : Dict → MPitch → SPitch
mp→np d (!! n) = n
mp→np d (?? s) with lookupE d s
... | +_ p     = pitch→np p
... | -[1+_] _ = pitch→np 0

-- Pairs and pairs of pairs of MPitch
MP MPMP LP LPLP [M] [[M]] [L] [[L]] : Type
MP    = MPitch × MPitch
MPMP  = MP × MP
LP    = Located MPitch × Located MPitch
LPLP  = LP × LP
[M]   = List MPitch
[[M]] = List [M]
[L]   = List (Located MPitch)
[[L]] = List [L]

-- Triplets of MPitch
M3 = MPitch × MPitch × MPitch

{-
[n]→[p] : [N] → [P]
[n]→[p] = map name→pitch

[[n]]→[[p]] : [[N]] → [[P]]
[[n]]→[[p]] = map [n]→[p]
-}

lp→mp : LP → MP
lp→mp (located _ a , located _ b) = a , b

lplp→mpmp : LPLP → MPMP
lplp→mpmp (a , b) = lp→mp a , lp→mp b

mp→p : MP → (IExpr × IExpr)
mp→p (a , b) = name→iexpr a , name→iexpr b

mpmp→pp : MPMP → PP
mpmp→pp (a , b) = mp→p a , mp→p b

[l]→[m] : [L] → [M]
[l]→[m] = map unlocate

[[l]]→[[m]] : [[L]] → [[M]]
[[l]]→[[m]] = map [l]→[m]

-- Assumes higher voice is first; range starts with higher voice
lpRange : LP → Range
lpRange (located l1 _ , located l2 _) = rectangle l1 l2

-- Assumes higher voice is first; range starts with higher voice
lplpRange : LPLP → Range
lplpRange ((located l1 _ , located l2 _) , (located l3 _ , located l4 _)) = rectangle l1 l4
