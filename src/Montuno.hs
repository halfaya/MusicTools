{-# LANGUAGE UnicodeSyntax #-}

module Montuno where

import Note
import Chord
import TimedChord

double ∷ [Chord] → [Chord]
double = map (\c → merge [c, (transposeChord scaleSize c)])

-- add the base note of the first chord to the first chord, transposed up 2 octaves
add2octave ∷ [Chord] → [Chord]
add2octave (c@(Chord (n : ns)) : cs) = (appendNote (transpose (scaleSize * 2) n) c) : cs
add2octave cs                        = cs

baseOctave ∷ Chord
baseOctave = Chord $ map (Note . (* scaleSize)) [0, 1, 2]

makeUnit ∷ (Chord → [Chord]) → ScaleDegree → [Chord]
makeUnit f = add2octave . double . f . relativeChordToChord . diatonicTriad . (\d → (d, Octave 0))

make2 ∷ (Chord → [Chord]) → ScaleDegree → [Chord]
make2 f secondScaleDegree =
  let scaleDegrees = secondScaleDegree : map ScaleDegree [4, 3]
  in makeUnit f (ScaleDegree 0) ++ (scaleDegrees >>= makeUnit oompah) ++ [baseOctave]

rhythm, rhythma ∷ [Duration]
rhythm  = map Duration $ [2, 1]    ++ replicate 6 2 ++ [1]
rhythma = map Duration $ [1, 1, 1] ++ replicate 6 2 ++ [1]

ex8 ∷ [TimedChord]
ex8 = zip (make2 oompah (ScaleDegree 3)) rhythm

ex9 ∷ [TimedChord]
ex9 = zip (make2 arpegiate (ScaleDegree 3)) rhythma

ex10 ∷ [TimedChord]
ex10 = zip (make2 arpegiate (ScaleDegree 1)) rhythma ++ ex8
