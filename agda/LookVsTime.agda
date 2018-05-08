module LookVsTime where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_])
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length)
open import Data.Nat     using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_; uncurry)
open import Function     using (_∘_)

open import Pitch
open import Note
open import Music        hiding (map)

repeat : ∀ {a} {A : Set a} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

bassMelodyRel : List RelativePitch
bassMelodyRel = map (scaleDegreeToRelativePitch majorScale ∘ scaleDegree)
                 (# 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ [])

bassMelody : List Pitch
bassMelody = map (relativeToAbsolute ∘ (_, octave -[1+ 0 ])) bassMelodyRel

baseRhythm : List Duration
baseRhythm = map duration (+ 3 ∷ + 1 ∷ + 2 ∷ + 2 ∷ [])

bassNotes : List Note
bassNotes = repeat 28 (map (uncurry note) (zip baseRhythm bassMelody))

drumRhythmA : List Duration
drumRhythmA = map duration (+ 2 ∷ [])

drumRhythmB : List Duration
drumRhythmB = map duration (+ 1 ∷ + 1 ∷ + 2 ∷ [])

drumRhythm : List Duration
drumRhythm = drumRhythmA ++ repeat 3 drumRhythmB ++ drumRhythmA

drumPitches : List Pitch
drumPitches = replicate (length drumRhythm) (pitch -[1+ 0 ]) -- Ride In

drumNotes : List Note
drumNotes = rest (duration (+ 16)) ∷ repeat 27 (map (uncurry note) (zip drumRhythm drumPitches))

lookVsTime : Music
lookVsTime = fromNotes bassNotes
