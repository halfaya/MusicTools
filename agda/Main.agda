{-# OPTIONS --erased-cubical #-}

module Main where

open import Prelude
open import IO.Primitive

open import Beethoven
open import Kennan
open import Tanaka
open import Counterpoint using (defaultConstraints)
open import Midi         using (exportTracks; track→htrack)
open import MidiEvent    using (counterpoint→events; events→tracks; defaultVelocity)
open import Note         using (half; whole)
open import SmtInterface using (solveToMidi)

main : IO ⊤
main = do
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      tempo        = 240
      file         = "/Users/leo/Music/MusicTools/test.mid"
  let events       = counterpoint→events defaultVelocity beethoven146c
  let song         = toList (events→tracks {4} {s≤s (s≤s (s≤s (s≤s z≤n)))} tempo events)
--  song             ← solveToMidi whole defaultConstraints k2-1
  exportTracks file ticksPerBeat (map track→htrack song)
