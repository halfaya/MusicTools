{-# OPTIONS --erased-cubical #-}

module Main where

open import Data.List using (map)
open import Data.Unit using (⊤)
open import IO.Primitive

open import Beethoven
open import Midi         using (exportTracks; track→htrack)
open import SmtInterface using (firstSpecies→Midi)

main : IO ⊤
main = do
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
  song             ← firstSpecies→Midi beethoven146cf
  exportTracks file ticksPerBeat (map track→htrack song)
