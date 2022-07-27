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

-- TODO: Remove
open import Data.Integer using (ℤ)
open import Agda.Builtin.Int using (primShowInteger)
open import Data.String using (String)
process : List (HMaybe ℤ) → String
process []       = ""
process (just x ∷ xs) = primShowInteger x
process (nothing ∷ xs) = "nothing"

main : IO ⊤
main =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = firstSpecies→Midi beethoven146-1
  in exportTracks file ticksPerBeat (map track→htrack song)

{-
main : IO ⊤
main = do
  args ← getArgs
  (putStrLn ∘ process2 ∘ (λ x → solveConstraints x ((var "var2" == # (+ 14)) ∷ []))) args

main' : IO ⊤
main' =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = ycpTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
-}
