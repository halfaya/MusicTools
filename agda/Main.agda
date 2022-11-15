{-# OPTIONS --erased-cubical #-}

module Main where

open import Prelude
open import IO.Primitive

open import Beethoven
open import Kennan
open import Tanaka
open import Counterpoint using (defaultConstraints)
open import Location     using (indexVoiceBeat; location; rectangle)
open import Midi         using (exportTracks; track→htrack)
open import Misc         using (makeVariables)
open import MidiEvent    using (counterpoint→events; events→tracks; defaultVelocity)
open import Note         using (half; whole)
open import SmtInterface using (solveToMidi)

main : IO ⊤
main = do
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      range        = rectangle (location 2 2) (location 4 11)
      source       = makeVariables range (indexVoiceBeat (take 3 beethoven146))
  song             ← solveToMidi half defaultConstraints source
  exportTracks file ticksPerBeat (map track→htrack song)
