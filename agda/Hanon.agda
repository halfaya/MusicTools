{-# OPTIONS --without-K --safe #-}

module Hanon where

open import Data.Fin     using (#_)
open import Data.Integer using (+_)
open import Data.List    using (List; _∷_; []; map; concat; _++_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_,_; map₁)
open import Data.Vec     using (fromList)
open import Function     using (_∘_)

open import Pitch        using (Pitch; octave; relativeToAbsolute; majorScale)
open import Note         using (8th)
open import Music        using (Melody; Counterpoint; cp; pitches→melody; transposeMelody)
open import MidiEvent    using (Channel-1; InstrumentNumber-1; MidiTrack; track; counterpoint→events; defaultVelocity)
open import ScaleDegree  using (ScaleDegreeOctave; scaleDegree; transposeScaleDegree; scaleDegreeToPitchClass)

cell : List (ScaleDegreeOctave 7)
cell = map (_, octave 3) (map (scaleDegree) (# 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ # 5 ∷ # 4 ∷ # 3 ∷ # 2 ∷ []))

0toN : ℕ → List ℕ
0toN zero    = 0 ∷ []
0toN (suc n) = 0toN n ++ (suc n) ∷ []

tcell : ℕ → List (ScaleDegreeOctave 7)
tcell n = map (transposeScaleDegree n) cell

half1scale : List (ScaleDegreeOctave 7)
half1scale = concat (map tcell (0toN 13))

half1pitches : List Pitch
half1pitches = map (relativeToAbsolute ∘ map₁ (scaleDegreeToPitchClass majorScale)) half1scale

half1bot half1top : Melody 224
half1bot = pitches→melody 8th (fromList half1pitches)
half1top = transposeMelody (+ 12) half1bot

hanon1 : Counterpoint 2 224
hanon1 = cp (fromList (half1bot ∷ half1top ∷ []))

----

instrument : InstrumentNumber-1
instrument = # 0 -- piano

channel : Channel-1
channel = # 0

tempo : ℕ
tempo = 180

hanonTrack : List MidiTrack
hanonTrack = track "Piano" instrument channel tempo (counterpoint→events defaultVelocity hanon1) ∷ []
