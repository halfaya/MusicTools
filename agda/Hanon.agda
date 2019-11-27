{-# OPTIONS --without-K #-}

module Hanon where

open import Data.Fin     using (Fin; #_)
open import Data.Integer using (+_; -[1+_]; ℤ)
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; foldr)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; map₁)
open import Data.Vec     using (fromList)
open import Function     using (_∘_)

open import Pitch
open import Note
open import Music
open import MidiEvent
open import ScaleDegree
open import Util

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
half1pitches = map (relativeToAbsolute ∘ map₁ (scaleDegreeToRelativePitch majorScale)) half1scale

half1bot half1top : Melody 224
half1bot = pitches→melody 8th (fromList half1pitches)
half1top = transposeMelody (+ 12) half1bot

hanon1 : Music 2 224
hanon1 = music (fromList (half1bot ∷ half1top ∷ []))

----

instrument : InstrumentNumber-1
instrument = # 0 -- piano

channel : Channel-1
channel = # 0

tempo : ℕ
tempo = 180

hanonTrack : List MidiTrack
hanonTrack = track "Piano" instrument channel tempo (music→events defaultVelocity hanon1) ∷ []
