{-# OPTIONS --without-K #-}

module Music where

open import Data.Integer using (ℤ; +_)
open import Data.List    using (List; foldr; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Note         renaming (transpose to transposeNote)
open import Pitch        renaming (transpose to transposePitch)

data Music : Set where
  note : Note → Music
  _∷_  : Music → Music → Music -- sequential composition
  _∥_  : Music → Music → Music -- parallel   composition

infixr 5 _∷_ _∥_

-- empty music as a basis for fold
nil : Music
nil = note (rest (duration 0))

lift : (Note → Note) → Music → Music
lift f (note n) = note (f n)
lift f (m ∷ m') = lift f m ∷ lift f m'
lift f (m ∥ m') = lift f m ∥ lift f m'

transpose : ℤ → Music → Music
transpose k = lift (transposeNote k)

buildMusic : {A : Set} → (A → Music) → List A → Music
buildMusic f = foldr (λ x m → f x ∷ m) nil

-- adds a duration 0 rest at the end which should be removed or ignored
fromNotes : List Note → Music
fromNotes = buildMusic note

data Chord : Set where
  chord : Duration → List Pitch → Chord

fromChord : Chord → Music
fromChord (chord d ps) = foldr (λ p m → note (tone d p) ∥ m) nil ps

fromChords : List Chord → Music
fromChords = buildMusic fromChord

-- TODO: Fix this.
-- unzip parallel lines as far as possible
unzip : Music → Music × Music
unzip (note _)                = nil , nil
unzip (note _ ∷ _)            = nil , nil
unzip (((note n ∥ note o) ∷ b) ∷ c) = let (x , y) = unzip (b ∷ c) in note n ∷ x , note o ∷ y
unzip ((a ∷ b) ∷ c)           = nil , nil
unzip ((note n ∥ note o) ∷ m) = let (x , y) = unzip m in note n ∷ x , note o ∷ y
unzip ((note _ ∥ _ ∷ _) ∷ _)  = nil , nil
unzip ((note _ ∥ _ ∥ _) ∷ _)  = nil , nil
unzip (((_ ∷ _) ∥ _) ∷ _)     = nil , nil
unzip (((_ ∥ _) ∥ _) ∷ _)     = nil , nil
unzip (note n ∥ note o)       = note n , note o
unzip (note _ ∥ _ ∷ _)        = nil , nil
unzip (note _ ∥ _ ∥ _)        = nil , nil
unzip ((_ ∷ _) ∥ _)           = nil , nil
unzip ((_ ∥ _) ∥ _)           = nil , nil

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
