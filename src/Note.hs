{-# LANGUAGE UnicodeSyntax #-}

module Note where

-- Position of a note on an absolute scale; 0 is later mapped to a base frequency.
newtype Note = Note Int
  deriving (Eq, Show)

unNote ∷ Note → Int
unNote (Note n) = n

-- Number of steps in the scale (in this case chromatic).
-- Currently this must be 12.
scaleSize ∷ Int
scaleSize = 12

-- Position of a note within an octave, in the range [0..scalesize-1].
-- This is enforced by always computing mod scaleSize.
newtype RelativeNote = RelativeNote Int

-- Which octave one is in.
newtype Octave = Octave Int

type NoteOctave = (RelativeNote, Octave)

relativeToAbsolute ∷ NoteOctave → Note
relativeToAbsolute (RelativeNote n, Octave o) = Note $ o * scaleSize + n `mod` scaleSize

absoluteToRelative ∷ Note → NoteOctave
absoluteToRelative (Note n) = (RelativeNote $ n `div` scaleSize, Octave $ n `mod` scaleSize)

diatonicScale ∷ [RelativeNote]
diatonicScale = map RelativeNote [0, 2, 4, 5, 7, 9, 11]

diatonicScaleSize ∷ Int
diatonicScaleSize = length diatonicScale

newtype ScaleDegree = ScaleDegree Int -- 0 to 6
  deriving (Eq, Show)

type ScaleDegreeOctave = (ScaleDegree, Octave)

scaleDegreeToRelativeNote ∷ ScaleDegree → RelativeNote
scaleDegreeToRelativeNote (ScaleDegree d) = diatonicScale !! d

-- TODO: Check that this works with negative k.
addToDiatonicNote ∷ Int → ScaleDegreeOctave → ScaleDegreeOctave
addToDiatonicNote k (ScaleDegree d, Octave o) =
  (ScaleDegree $ (d + k) `mod` diatonicScaleSize, Octave $ o + (d + k) `div` diatonicScaleSize)

transpose ∷ Int → Note → Note
transpose k (Note n) = Note (n + k)

