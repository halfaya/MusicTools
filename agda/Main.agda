{-# OPTIONS --erased-cubical #-}

module Main where

open import Data.List using (map)

open import Midi      using (IO; _>>=_; getArgs; putStrLn; Unit; exportTracks; track→htrack)

open import FarmCanon using (canonTracks)
open import FarmFugue using (fugueTracks)

-- TODO: Remove
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Function using (_∘_)
open import Midi using (readNat)
open import Pitch using (toPC; showPC)
open import Agda.Builtin.Nat using (zero; suc)
process : List String → String
process []       = ""
process (x ∷ xs) with readNat x
... | zero  = ""
... | suc n = (showPC ∘ toPC) n

main : IO Unit
main = do
  args ← getArgs
  (putStrLn ∘ process) args

main' : IO Unit
main' =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = fugueTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
