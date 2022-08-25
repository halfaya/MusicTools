{-# OPTIONS --erased-cubical --safe #-}

module Symbolic where

open import Prelude

open import Expr hiding (_+_)
open import Pitch
open import Interval

-- Named Pitch
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
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = Min10
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = Maj10
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))) = Per11
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))) = Aug11
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))) = Per12
upi→name (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))) =
  Int (20 + n)

nint : NPitch → NPitch → NInt
nint a b = upi→name (upi (name→p a) (name→p b))
