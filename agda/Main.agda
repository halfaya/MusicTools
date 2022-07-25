{-# OPTIONS --erased-cubical #-}

module Main where

open import Data.List using (map)
open import Data.Unit using (⊤)

open import Midi      using (IO; _>>=_; getArgs; putStrLn; exportTracks; track→htrack)
open import Smt       using (solveConstraints; HMaybe; just; nothing; _==_; var; #_)

-- TODO: Remove
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Agda.Builtin.Int using (primShowInteger)
open import Agda.Builtin.String using (primShowNat)
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

process2 : List (HMaybe ℤ) → String
process2 []       = ""
process2 (just x ∷ xs) = primShowInteger x
process2 (nothing ∷ xs) = "nothing"

main : IO ⊤
main = do
  args ← getArgs
  (putStrLn ∘ process2 ∘ (λ x → solveConstraints x ((var "var2" == # (+ 14)) ∷ []))) args

{-
main' : IO ⊤
main' =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = ycpTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
-}
