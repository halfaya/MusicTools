module Music where

open import Data.Integer using (ℤ; +_)
open import Data.List    using (List; foldr; []; _∷_)

open import Note         renaming (transpose to transposeNote)
open import Pitch        renaming (transpose to transposePitch)

data Music : Set where
  note : Note → Music
  _∷_  : Music → Music → Music -- sequential composition
  _∥_  : Music → Music → Music -- parallel   composition

infixr 5 _∷_ _∥_

map : (Note → Note) → Music → Music
map f (note n) = note (f n)
map f (m ∷ m') = map f m ∷ map f m'
map f (m ∥ m') = map f m ∥ map f m'

transpose : ℤ → Music → Music
transpose k = map (transposeNote k)

-- adds a duration 0 rest at the end which should be removed or ignored
fromNotes : List Note → Music
fromNotes = foldr (λ n m → note n ∷ m) (note (rest (duration 0)))

data Chord : Set where
  chord : Duration → List Pitch → Chord

fromChord : Chord → Music
fromChord (chord d ps) = foldr (λ p m → note (note d p) ∥ m) (note (rest (duration 0))) ps

fromChords : List Chord → Music
fromChords = foldr (λ c m → fromChord c ∷ m) (note (rest (duration 0)))

{-
oompah : Chord → List Chord
oompah (chord [])       = []
oompah (chord (n ∷ ns)) = chord (n ∷ []) ∷ chord ns ∷ []

-- convert a chord to a series of single note chords
arpegiate : Chord → List Chord
arpegiate = map toChord ∘ unChord

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
-}
