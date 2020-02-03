{-# OPTIONS --without-K #-}

module Fmmh where

open import Data.List using (List)

open import Pitch

-- Reconstruction of "Functional Modelling of Musical Harmony" (ICFP 2011)
-- using similar notation. Original code:
-- https://github.com/chordify/HarmTrace-Base

data Mode : Set where
  maj : Mode
  min : Mode

data ChordQuality : Set where
  maj  : ChordQuality
  min  : ChordQuality
  dom7 : ChordQuality
  dim  : ChordQuality

data Chord : DiatonicDegree → ChordQuality → Set where
  chord : (d : DiatonicDegree) → (q : ChordQuality) → Chord d q

data Ton : Mode → Set where
  maj : Chord I maj → Ton maj
  min : Chord I min → Ton min

data SDom : Mode → Set where
  ii     : Chord II min → SDom maj
  iv-maj : Chord IV maj → SDom maj
  iii-iv : Chord III min → Chord IV maj → SDom maj
  iv-min : Chord IV min → SDom min

data Dom (m : Mode) : Set where
  v7   : Chord V dom7 → Dom m
  v    : Chord V maj → Dom m
  vii  : Chord VII dim → Dom m
  sdom : SDom m → Dom m → Dom m
  ii-v : Chord II dom7 → Chord V dom7 → Dom m

data Phrase (m : Mode) : Set where
  i-v-i : Ton m → Dom m → Ton m → Phrase m
  v-i   : Dom m → Ton m → Phrase m

data Piece : Set where
  piece : {m : Mode} → List (Phrase m) → Piece
