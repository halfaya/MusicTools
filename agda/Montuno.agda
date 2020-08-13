{-# OPTIONS --cubical #-}

module Montuno where

open import Data.Fin using (#_)
open import Data.Integer using (+_)
open import Data.List using (List; _∷_; []; map; concat; _++_; replicate; zip)
open import Data.Nat using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import Note

{-
double : List Chord → List Chord
double = map (λ c → flatten (c ∷ (transposeChord (+ chromaticScaleSize) c) ∷ []))

-- add the base note of the first chord to the first chord, transposed up 2 octaves
add2octave :  List Chord → List Chord
add2octave []                        = []
add2octave cs@(chord [] ∷ _)         = cs
add2octave (c@(chord (n ∷ ns)) ∷ cs) = (appendNote (transpose (+ (chromaticScaleSize * 2)) n) c) ∷ cs

baseOctave : Chord
baseOctave = chord (map (note ∘ +_ ∘ (_* chromaticScaleSize)) (0 ∷ 1 ∷ 2 ∷ []))

makeUnit : {n : ℕ} → Scale (suc n) → (Chord → List Chord) → ScaleDegree (suc n) → List Chord
makeUnit scale f = add2octave ∘ double ∘ f ∘ relativeChordToChord ∘ triad scale ∘ (λ d → (d , octave (+ 0)))

-- TODO: See if we can use the one in Data.List
_≫=_ : {A B : Set} → List A → (A → List B) → List B
xs ≫= f = concat (map f xs)

make2 : {n : ℕ} → Scale (5 + n) → (Chord → List Chord) → ScaleDegree (5 + n) → List Chord
make2 scale f secondScaleDegree =
  let scaleDegrees = secondScaleDegree ∷ map scaleDegree (# 4 ∷ # 3 ∷ [])
  in makeUnit scale f (scaleDegree (# 0)) ++ (scaleDegrees ≫= makeUnit scale oompah) ++ (baseOctave ∷ [])

rhythm rhythma : List Duration
rhythm  = map duration (+ 2       ∷ + 1 ∷ (replicate 6 (+ 2) ++ (+ 1 ∷ [])))
rhythma = map duration (+ 1 ∷ + 1 ∷ + 1 ∷ (replicate 6 (+ 2) ++ (+ 1 ∷ [])))

ex8 ex9 ex10 : {n : ℕ} → Scale (5 + n) → List TimedChord
ex8  scale = zip (make2 scale oompah    (scaleDegree (# 3))) rhythm
ex9  scale = zip (make2 scale arpegiate (scaleDegree (# 3))) rhythm
ex10 scale = zip (make2 scale arpegiate (scaleDegree (# 1))) rhythma ++ ex8 scale
-}
