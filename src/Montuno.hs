{-# LANGUAGE UnicodeSyntax #-}

module Montuno where

import Note
import Chord
import TimedChord

double ∷ [Chord] → [Chord]
double = map (\c → flatten [c, (transposeChord chromaticScaleSize c)])

-- add the base note of the first chord to the first chord, transposed up 2 octaves
add2octave ∷ [Chord] → [Chord]
add2octave (c@(Chord (n : ns)) : cs) = (appendNote (transpose (chromaticScaleSize * 2) n) c) : cs
add2octave cs                        = cs

baseOctave ∷ Chord
baseOctave = Chord $ map (Note . (* chromaticScaleSize)) [0, 1, 2]

makeUnit ∷ Scale → (Chord → [Chord]) → ScaleDegree → [Chord]
makeUnit scale f = add2octave . double . f . relativeChordToChord . triad scale . (\d → (d, Octave 0))

make2 ∷ Scale → (Chord → [Chord]) → ScaleDegree → [Chord]
make2 scale f secondScaleDegree =
  let scaleDegrees = secondScaleDegree : map ScaleDegree [4, 3]
  in makeUnit scale f (ScaleDegree 0) ++ (scaleDegrees >>= makeUnit scale oompah) ++ [baseOctave]

rhythm, rhythma ∷ [Duration]
rhythm  = map Duration $ [2, 1]    ++ replicate 6 2 ++ [1]
rhythma = map Duration $ [1, 1, 1] ++ replicate 6 2 ++ [1]

ex8 ∷ Scale → [TimedChord]
ex8 scale = zip (make2 scale oompah (ScaleDegree 3)) rhythm

ex9 ∷ Scale → [TimedChord]
ex9 scale = zip (make2 scale arpegiate (ScaleDegree 3)) rhythma

ex10 ∷ Scale → [TimedChord]
ex10 scale = zip (make2 scale arpegiate (ScaleDegree 1)) rhythma ++ ex8 scale
