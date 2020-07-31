{-# OPTIONS --without-K #-}

module Main where

open import Data.List using (map)

open import Midi      using (IO; Unit; exportTracks; track→htrack)

open import FarmCanon using (canonTracks)
open import FarmFugue using (fugueTracks)

main : IO Unit
main =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = fugueTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
