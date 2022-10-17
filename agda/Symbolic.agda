{-# OPTIONS --erased-cubical --safe #-}

module Symbolic where

open import Prelude

open import Expr hiding (_+_; #_)
open import Pitch
open import Interval

-- Named Pitch
data NoteName : Type where
  C  : NoteName
  C♯ : NoteName
  D♭ : NoteName
  D  : NoteName
  D♯ : NoteName
  E♭ : NoteName
  E  : NoteName
  F  : NoteName
  F♯ : NoteName
  G♭ : NoteName
  G  : NoteName
  G♯ : NoteName
  A♭ : NoteName
  A  : NoteName
  A♯ : NoteName
  B♭ : NoteName
  B  : NoteName

showNoteName : NoteName → String
showNoteName C  = "C"
showNoteName C♯ = "C♯"
showNoteName D♭ = "D♭"
showNoteName D  = "D"
showNoteName D♯ = "D♯"
showNoteName E♭ = "E♭"
showNoteName E  = "E"
showNoteName F  = "F"
showNoteName F♯ = "F♯"
showNoteName G♭ = "G♭"
showNoteName G  = "G"
showNoteName G♯ = "G♯"
showNoteName A♭ = "A♭"
showNoteName A  = "A"
showNoteName A♯ = "A♯"
showNoteName B♭ = "B♭"
showNoteName B  = "B"

noteName→PC : NoteName → PC
noteName→PC C  = # 0
noteName→PC C♯ = # 1
noteName→PC D♭ = # 1
noteName→PC D  = # 2
noteName→PC D♯ = # 3
noteName→PC E♭ = # 3
noteName→PC E  = # 4
noteName→PC F  = # 5
noteName→PC F♯ = # 6
noteName→PC G♭ = # 6
noteName→PC G  = # 7
noteName→PC G♯ = # 8
noteName→PC A♭ = # 8
noteName→PC A  = # 9
noteName→PC A♯ = # 10
noteName→PC B♭ = # 10
noteName→PC B  = # 11

-- Named Pitch
-- We don't use a product type here since it would be more verbose.
data NPitch : Type where
  C  : Octave → NPitch
  C♯ : Octave → NPitch
  D♭ : Octave → NPitch
  D  : Octave → NPitch
  D♯ : Octave → NPitch
  E♭ : Octave → NPitch
  E  : Octave → NPitch
  F  : Octave → NPitch
  F♯ : Octave → NPitch
  G♭ : Octave → NPitch
  G  : Octave → NPitch
  G♯ : Octave → NPitch
  A♭ : Octave → NPitch
  A  : Octave → NPitch
  A♯ : Octave → NPitch
  B♭ : Octave → NPitch
  B  : Octave → NPitch
  ?? : String → NPitch -- unknown note with a unique variable name

showNPitch : NPitch → String
showNPitch (C  o) = "C"  ++s primShowNat o
showNPitch (C♯ o) = "C♯" ++s primShowNat o
showNPitch (D♭ o) = "D♭" ++s primShowNat o
showNPitch (D  o) = "D"  ++s primShowNat o
showNPitch (D♯ o) = "D♯" ++s primShowNat o
showNPitch (E♭ o) = "E♭" ++s primShowNat o
showNPitch (E  o) = "E"  ++s primShowNat o
showNPitch (F  o) = "F"  ++s primShowNat o
showNPitch (F♯ o) = "F♯" ++s primShowNat o
showNPitch (G♭ o) = "G♭" ++s primShowNat o
showNPitch (G  o) = "G"  ++s primShowNat o
showNPitch (G♯ o) = "G♯" ++s primShowNat o
showNPitch (A♭ o) = "A♭" ++s primShowNat o
showNPitch (A  o) = "A"  ++s primShowNat o
showNPitch (A♯ o) = "A♯" ++s primShowNat o
showNPitch (B♭ o) = "B♭" ++s primShowNat o
showNPitch (B  o) = "B"  ++s primShowNat o
showNPitch (?? s) = "?"  ++s s

noteName→npitch : NoteName → Octave → NPitch
noteName→npitch C  o = C  o
noteName→npitch C♯ o = C♯ o
noteName→npitch D♭ o = D♭ o
noteName→npitch D  o = D  o
noteName→npitch D♯ o = D♯ o
noteName→npitch E♭ o = E♭ o
noteName→npitch E  o = E  o
noteName→npitch F  o = F  o
noteName→npitch F♯ o = F♯ o
noteName→npitch G♭ o = G♭ o
noteName→npitch G  o = G  o
noteName→npitch G♯ o = G♯ o
noteName→npitch A♭ o = A♭ o
noteName→npitch A  o = A  o
noteName→npitch A♯ o = A♯ o
noteName→npitch B♭ o = B♭ o
noteName→npitch B  o = B  o

npitch→noteName : NPitch → NoteName
npitch→noteName (C  o) = C
npitch→noteName (C♯ o) = C♯
npitch→noteName (D♭ o) = D♭
npitch→noteName (D  o) = D
npitch→noteName (D♯ o) = D♯
npitch→noteName (E♭ o) = E♭
npitch→noteName (E  o) = E
npitch→noteName (F  o) = F
npitch→noteName (F♯ o) = F♯
npitch→noteName (G♭ o) = G♭
npitch→noteName (G  o) = G
npitch→noteName (G♯ o) = G♯
npitch→noteName (A♭ o) = A♭
npitch→noteName (A  o) = A
npitch→noteName (A♯ o) = A♯
npitch→noteName (B♭ o) = B♭
npitch→noteName (B  o) = B
npitch→noteName (?? s) = C -- make this C for now; should fix this somewhow

name→pitch : NPitch → IExpr
name→pitch (C  o) = N (o * s12 + 0)
name→pitch (C♯ o) = N (o * s12 + 1)
name→pitch (D♭ o) = N (o * s12 + 1)
name→pitch (D  o) = N (o * s12 + 2)
name→pitch (D♯ o) = N (o * s12 + 3)
name→pitch (E♭ o) = N (o * s12 + 3)
name→pitch (E  o) = N (o * s12 + 4)
name→pitch (F  o) = N (o * s12 + 5)
name→pitch (F♯ o) = N (o * s12 + 6)
name→pitch (G♭ o) = N (o * s12 + 6)
name→pitch (G  o) = N (o * s12 + 7)
name→pitch (G♯ o) = N (o * s12 + 8)
name→pitch (A♭ o) = N (o * s12 + 8)
name→pitch (A  o) = N (o * s12 + 9)
name→pitch (A♯ o) = N (o * s12 + 10)
name→pitch (B♭ o) = N (o * s12 + 10)
name→pitch (B  o) = N (o * s12 + 11)
name→pitch (?? s) = var s

name→pitch2 : NPitch × NPitch → IExpr × IExpr
name→pitch2 (a , b ) = name→pitch a , name→pitch b

-- Variables map to pitch 0
name→p : NPitch → Pitch
name→p np with evalI (name→pitch np)
... | +_     n = n
... | -[1+_] _ = 0

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

nint : NPitch → NPitch → NInt
nint a b = upi→name (upi (name→p a) (name→p b))

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
scale (key C major) = C ∷ D ∷ E ∷ F ∷ G ∷ A ∷ B ∷ []
scale (key F major) = F ∷ G ∷ A ∷ B♭ ∷ C ∷ D ∷ E ∷ []
scale (key G major) = G ∷ A ∷ B ∷ C ∷ D ∷ E ∷ F♯ ∷ []

chromaticScale : Vec NoteName s12
chromaticScale = C ∷ C♯ ∷ D ∷ E♭ ∷ E ∷ F ∷ F♯ ∷ G ∷ A♭ ∷ A ∷ B♭ ∷ B ∷ []

toScale : {n : ℕ} → Vec NoteName n → Scale n
toScale = vmap noteName→PC

pitch→npitch : Pitch → NPitch
pitch→npitch n =
  let (p , o) = absoluteToRelative n
  in noteName→npitch (lookup chromaticScale p) o
