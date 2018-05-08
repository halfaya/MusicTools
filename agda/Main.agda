module Main where

open import Data.Integer using (_-_; +_)

open import Note
open import TimedChord
open import Midi

open import Montuno
open import LookVsTime

main : IO Unit
main =
  let channel      = + 0
      ticksPerBeat = + 4 -- 16th notes
      song         = transposeTimedChords middleC drumChords
      file         = "/Users/leo/Downloads/test.mid"
  in exportSong file channel ticksPerBeat (toHTimedChords song)
