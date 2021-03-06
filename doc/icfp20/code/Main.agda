{-# OPTIONS --without-K #-}

module Main where

open import Data.List

open import Midi
open import Note

open import Frog
open import Piston

main : IO Unit
main =
  let channel      = 0
      ticksPerBeat = 4 -- 16th notes
      file         = "/tmp/test.mid"
-- counterpoint
      song         = cfcpTracks1
--      song         = cfcpTracks2
-- harmony
--      song         = testHTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
