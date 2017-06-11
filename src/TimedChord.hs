{-# LANGUAGE UnicodeSyntax, GADTSyntax #-}

module TimedChord where

import Data.Bifunctor (first)

import Note
import Chord

-- duration in some unspecified unit
newtype Duration = Duration Int
  deriving (Eq, Show)

type TimedChord = (Chord, Duration)

transposeTimedChord ∷ Int → TimedChord → TimedChord
transposeTimedChord = first . transposeChord

transposeTimedChords ∷ Int → [TimedChord] → [TimedChord]
transposeTimedChords = map . transposeTimedChord

