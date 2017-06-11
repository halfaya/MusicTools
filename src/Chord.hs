{-# LANGUAGE UnicodeSyntax #-}

module Chord where

import Data.Bifunctor (first)

import Note

newtype Chord = Chord [Note]
  deriving (Eq, Show)

unChord ∷ Chord → [Note]
unChord (Chord ns) = ns

newtype RelativeChord = RelativeChord [NoteOctave]

transposeChord ∷ Int → Chord → Chord
transposeChord k (Chord ns) = Chord $ map (transpose k) ns

oompah ∷ Chord → [Chord]
oompah (Chord (n : ns)) = [Chord [n], Chord ns]
oompah (Chord [])       = []

-- convert a chord to a series of single note chords
arpegiate ∷ Chord → [Chord]
arpegiate = map (Chord . (:[])) . unChord

makeChord ∷ [Int] → Note → Chord
makeChord ks (Note n) =  Chord $ map (Note . (n+)) ks

majorTriad ∷ Note → Chord
majorTriad = makeChord [0, 4, 7]

minorTriad ∷ Note → Chord
minorTriad = makeChord [0, 3, 7]

merge ∷ [Chord] → Chord
merge = Chord . concat . (map unChord)

prependNote ∷ Note → Chord → Chord
prependNote n (Chord ns) = Chord (n : ns)

appendNote ∷ Note → Chord → Chord
appendNote n (Chord ns) = Chord (ns ++ [n])

diatonicTriad ∷ ScaleDegreeOctave → RelativeChord
diatonicTriad sdo =
  let scaleChord = map ((flip addToDiatonicNote) sdo) [0, 2, 4]
  in RelativeChord $ map (first scaleDegreeToRelativeNote) scaleChord

relativeChordToChord ∷ RelativeChord → Chord
relativeChordToChord (RelativeChord c) = Chord (map relativeToAbsolute c)
