{-# OPTIONS --cubical --safe #-}

module Fmmh where

open import Data.List using (List)

open import Diatonic
open import Pitch

-- Reconstruction of "Functional Modelling of Musical Harmony" (ICFP 2011)
-- using similar notation. Original code:
-- https://github.com/chordify/HarmTrace-Base

data ChordQuality : Set where
  maj  : ChordQuality
  min  : ChordQuality
  dom7 : ChordQuality
  dim  : ChordQuality

data Chord : DiatonicDegree → ChordQuality → Set where
  chord : (d : DiatonicDegree) → (q : ChordQuality) → Chord d q

data Ton : Mode → Set where
  major : Chord d1 maj → Ton major
  minor : Chord d1 min → Ton minor

data SDom : Mode → Set where
  ii     : Chord d2 min → SDom major
  iv-maj : Chord d4 maj → SDom major
  iii-iv : Chord d3 min → Chord d4 maj → SDom major
  iv-min : Chord d4 min → SDom minor

data Dom (m : Mode) : Set where
  v7   : Chord d5 dom7 → Dom m
  v    : Chord d5 maj → Dom m
  vii  : Chord d7 dim → Dom m
  sdom : SDom m → Dom m → Dom m
  ii-v : Chord d2 dom7 → Chord d5 dom7 → Dom m

data Phrase (m : Mode) : Set where
  i-v-i : Ton m → Dom m → Ton m → Phrase m
  v-i   : Dom m → Ton m → Phrase m

data Piece : Set where
  piece : {m : Mode} → List (Phrase m) → Piece
