{-# OPTIONS --without-K  --allow-exec #-}

module Exec where

open import Reflection

open import Prelude

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
           → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}

macro
  readFile : String → Term → TC ⊤
  readFile file hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "cat" (file ∷ []) ""
    unify hole (lit (string stdOut))

fileName : String
fileName = "/Users/leo/Downloads/Test 1.xml"

s : String
s = readFile fileName
