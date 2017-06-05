{-# LANGUAGE UnicodeSyntax #-}

module Chord where

import Note

type Chord = [AbsoluteNote]

-- Should be a set.
type RelativeChord = [RelativeNote]

type ScaleDegree = Int -- 0 to 6

-- for each scale degree, it's offset from the root
offset ∷ [Int]
offset = diatonicScale

-- k is how many times to repeat, starting at oct and going up.
baseNotes ∷ Octave → ScaleDegree → Int → Chord
baseNotes oct sd k = map (\o → relativeToAbsolute (offset !! sd, o)) [oct..oct+k-1]
