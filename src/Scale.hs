{-# LANGUAGE UnicodeSyntax, GADTs #-}

-- Number of steps in the scale (in this case chromatic)
scaleSize ∷ Int
scaleSize = 12

-- Position of a note within an octave, in the range [0..scalesize-1].
-- This is enforced by always computing mod scaleSize.
type RelativeNote = Int

-- Which octave one is in.
type Octave = Int

type NoteOctave = (RelativeNote, Octave)

-- Position of a note on an absolute scale; 0 is later mapped to a base frequency.
type AbsoluteNote = Int

relativeToAbsolute ∷ NoteOctave → AbsoluteNote
relativeToAbsolute (n, o) = o * scaleSize + n `mod` scaleSize

absoluteToRelative ∷ AbsoluteNote → NoteOctave
absoluteToRelative n = (n `div` scaleSize, n `mod` scaleSize)

diatonicScale ∷ [RelativeNote]
diatonicScale = [0, 2, 4, 5, 7, 9, 11]
