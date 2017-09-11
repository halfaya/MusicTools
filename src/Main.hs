{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Note
import TimedChord
import Midi
import Montuno
import Codec.Midi

main ∷ IO ()
main = do
  let channel      = 0
  let ticksPerBeat = 2
  let baseNote     = middleC - 12
  let song         = transposeTimedChords baseNote (ex10 harmonicMinorScale)
  let midi         = toMidi channel ticksPerBeat song
  --putStrLn $ show midi
  exportFile "test.mid" midi
