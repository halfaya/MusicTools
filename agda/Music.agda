{-# OPTIONS --without-K #-}

module Music where

open import Data.Nat     using (ℕ; zero; suc; _+_; _*_)
open import Data.Integer using (ℤ; +_)
open import Data.List    using (List; foldr; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Vec     using (Vec; []; _∷_; replicate; concat; map)
open import Function     using (_∘_)

open import Note  renaming (transpose to transposeNote)
open import Pitch renaming (transpose to transposePitch)

-- A point in the music grid, which can either be a tone,
-- a continuation of a previous tone, or a rest.
data Point : Set where
  tone : Pitch → Point
  cont : Pitch → Point
  rest : Point

data Melody (n : ℕ) : Set where
  melody : Vec Point n → Melody n

melodyPoints : {n : ℕ} → Melody n → Vec Point n
melodyPoints (melody ps) = ps

note→melody : (n : Note) → Melody (noteDuration n)
note→melody (tone (duration zero)    p) = melody []
note→melody (tone (duration (suc d)) p) = melody (tone p ∷ replicate (cont p))
note→melody (rest _)                    = melody (replicate rest)

pitches→melody : {n : ℕ} → (d : Duration) → (ps : Vec Pitch n) → Melody (n * duration→ℕ d)
pitches→melody d ps = melody (concat (map (melodyPoints ∘ note→melody ∘ tone d) ps))

-- Assumes melody is well-formed in that a continuation note has the
-- same pitch as the note before it.
{-
melody→notes : {n : ℕ} → Melody n → List Note
melody→notes (melody []) = []
melody→notes (melody (p ∷ ps)) = {!!}
-}

data Chord (n : ℕ) : Set where
  chord : Vec Point n → Chord n

-- Music is a v × d grid where v is the number of voices and d is the duration.
-- The primary representation is as parallel melodies (counterpoint).
data Music (v : ℕ) (d : ℕ): Set where
  music : Vec (Melody d) v → Music v d

-- An alternative representation of music is as a series of chords (harmony).
data Harmony (v : ℕ) (d : ℕ): Set where
  harmony : Vec (Chord v) d → Harmony v d

{-
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
-}
