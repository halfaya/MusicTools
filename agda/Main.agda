{-# OPTIONS --erased-cubical #-}

module Main where

open import Data.List using (List; []; _∷_; map)
open import Data.Unit using (⊤)

open import Midi      using (IO; _>>=_; getArgs; putStrLn; exportTracks; track→htrack)
open import Smt       using (solveConstraints; compileConstraints; HMaybe; just; nothing; _==_; var; #_; B→HBExpr)

open import Beethoven using (beethoven146-1)
open import Constraint
open import Counterpoint
open import SmtResult using (firstSpecies→Midi)

main : IO ⊤
main =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = firstSpecies→Midi beethoven146-1
  in exportTracks file ticksPerBeat (map track→htrack song)
