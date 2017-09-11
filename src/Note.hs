{-# LANGUAGE UnicodeSyntax #-}

module Note where

-- Position of a note on an absolute scale; 0 is later mapped to a base frequency.
newtype Note = Note Int
  deriving (Eq, Show)

unNote ∷ Note → Int
unNote (Note n) = n

-- Number of steps in the scale (in this case chromatic).
-- Currently this must be 12.
chromaticScaleSize ∷ Int
chromaticScaleSize = 12

-- Position of a note within an octave, in the range [0..scalesize-1].
-- This is enforced by always computing mod scaleSize.
newtype RelativeNote = RelativeNote Int

type Scale = [RelativeNote]

-- Which octave one is in.
newtype Octave = Octave Int

type NoteOctave = (RelativeNote, Octave)

relativeToAbsolute ∷ NoteOctave → Note
relativeToAbsolute (RelativeNote n, Octave o) = Note $ o * chromaticScaleSize + n `mod` chromaticScaleSize

absoluteToRelative ∷ Note → NoteOctave
absoluteToRelative (Note n) = (RelativeNote $ n `div` chromaticScaleSize, Octave $ n `mod` chromaticScaleSize)

majorScale ∷ Scale
majorScale = map RelativeNote [0, 2, 4, 5, 7, 9, 11]

harmonicMinorScale ∷ Scale
harmonicMinorScale = map RelativeNote [0, 2, 3, 5, 7, 8, 11]

scaleSize ∷ Scale → Int
scaleSize = length

newtype ScaleDegree = ScaleDegree Int -- 0 to 6
  deriving (Eq, Show)

type ScaleDegreeOctave = (ScaleDegree, Octave)

scaleDegreeToRelativeNote ∷ Scale → ScaleDegree → RelativeNote
scaleDegreeToRelativeNote scale (ScaleDegree d) = scale !! d

-- TODO: Check that this works with negative k.
addToScaleNote ∷ Int → Int → ScaleDegreeOctave → ScaleDegreeOctave
addToScaleNote scaleSize k (ScaleDegree d, Octave o) =
  (ScaleDegree $ (d + k) `mod` scaleSize, Octave $ o + (d + k) `div` scaleSize)

transpose ∷ Int → Note → Note
transpose k (Note n) = Note (n + k)

