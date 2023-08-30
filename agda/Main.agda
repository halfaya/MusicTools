{-# OPTIONS --without-K #-}

module Main where

open import Prelude
open import IO.Primitive

open import Beethoven
open import Counterpoint using (defaultConstraints)
open import Location     using (indexVoiceBeat; location; rectangle)
open import Midi         using (exportTracks; track→htrack)
open import MidiEvent    using (counterpoint→events; events→tracks; defaultVelocity)
open import Note         using (half; whole)
open import SmtInterface using (solveToMidi)
open import Variable     using (makeVars)

main : IO ⊤
main = do
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      range        = rectangle (location 2 2) (location 4 11)
      source       = makeVars range (indexVoiceBeat (take 3 beethoven146m))
--      range        = rectangle (location 1 2) (location 1 9)
--      source       = makeVars range (indexVoiceBeat tanaka)
  song             ← solveToMidi half defaultConstraints source
  exportTracks file ticksPerBeat (map track→htrack song)
