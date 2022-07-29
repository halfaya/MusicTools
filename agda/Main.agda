{-# OPTIONS --erased-cubical #-}

module Main where

open import Data.List using (map)
open import Data.Unit using (⊤)

open import Beethoven
open import Midi      using (IO; exportTracks; track→htrack)
open import SmtResult using (firstSpecies→Midi)

main : IO ⊤
main =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = firstSpecies→Midi beethoven146cf
  in exportTracks file ticksPerBeat (map track→htrack song)
