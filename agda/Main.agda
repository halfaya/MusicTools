{-# OPTIONS --without-K #-}

module Main where

open import Data.List

open import Midi
open import Note

open import Exercises
open import Hanon
--open import Montuno
open import LookVsTime
open import Yamanote
open import Frog
open import Piston

main : IO Unit
main =
  let channel      = 0
      ticksPerBeat = 4 -- 16th notes
--      file         = "/Users/youyoucong/Music/test.mid"
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = melody117Tracks
--      song         = cfcpTracks2
--      song         = ycpTracks
--      song         = hanonTrack
--      song         = lookVsTime
  in exportTracks file ticksPerBeat (map track→htrack song)
