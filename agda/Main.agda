module Main where

open import Data.Integer using (_-_; +_)
open import Data.List

open import Note
open import Midi

open import Montuno
open import LookVsTime

main : IO Unit
main =
  let channel      = + 0
      ticksPerBeat = + 4 -- 16th notes
      file         = "/Users/leo/Downloads/test.mid"
      song         = lookVsTime
  in exportTracks file ticksPerBeat (map track→htrack song)
