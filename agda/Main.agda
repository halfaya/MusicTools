module Main where

open import Data.Integer using (_-_; +_)

open import Note
open import TimedChord
open import Montuno
open import Midi

main : IO Unit
main =
  let channel      = + 0
      ticksPerBeat = + 2
      baseNote     = middleC - (+ 12)
      song         = transposeTimedChords baseNote (ex10 harmonicMinorScale)
      file         = "test.mid"
  in exportSong file channel ticksPerBeat (toHTimedChords song)
