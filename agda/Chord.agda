module Chord where

open import Data.Integer
open import Data.List
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁) renaming (map to pmap)
open import Function

open import Note

data Chord : Set where
  chord : List Note → Chord

unChord : Chord → List Note
unChord (chord ns) = ns

data RelativeChord : Set where
  relativeChord : List NoteOctave → RelativeChord

transposeChord : ℤ → Chord → Chord
transposeChord k (chord ns) = chord (map (transpose k) ns)

oompah : Chord → List Chord
oompah (chord [])       = []
oompah (chord (n ∷ ns)) = chord (n ∷ []) ∷ chord ns ∷ []

-- convert a chord to a series of single note chords
arpegiate : Chord → List Chord
arpegiate = map (chord ∘ (_∷ [])) ∘ unChord

makeChord : List ℤ → Note → Chord
makeChord ks (note n) = chord (map (note ∘ (_+ n)) ks)

majorTriad minorTriad : Note → Chord
majorTriad = makeChord (+ 0 ∷ + 4 ∷ + 7 ∷ [])
minorTriad = makeChord (+ 0 ∷ + 3 ∷ + 7 ∷ [])

flatten : List Chord → Chord
flatten = chord ∘ concat ∘ (map unChord)

prependNote : Note → Chord → Chord
prependNote n (chord ns) = chord (n ∷ ns)

appendNote : Note → Chord → Chord
appendNote n (chord ns) = chord (ns ++ (n ∷ []))

relativeChordToChord : RelativeChord → Chord
relativeChordToChord (relativeChord c) = chord (map relativeToAbsolute c)

triad : {n : ℕ} → Scale (ℕ.suc n) → ScaleDegreeOctave (ℕ.suc n) → RelativeChord
triad scale sdo =
  let scaleChord = map ((flip addToScaleNote) sdo) (+ 0 ∷ + 2 ∷ + 4 ∷ [])
  in relativeChord (map ((pmap (scaleDegreeToRelativeNote scale) id)) scaleChord)
