{-# OPTIONS --without-K --allow-exec #-}

module Exec where

open import Reflection using (TC; Term; _>>=_; unify; lit; string)

open import Expr
open import Prelude
open import Serial

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
           → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}

-- You must add the full path to the compiled HMusicTools to ~/.agda/executables to run these macros.
macro
  readFile : String → Term → TC ⊤ -- returns the contents of the file as a String
  readFile file hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" ("readXML" ∷ file ∷ []) ""
    unify hole (lit (string stdOut))

  -- vars is a list of variable names
  -- returns a space-separated list of integer values for each variable
  solve : List String → List BExpr → Term → TC ⊤
  solve vars constraints hole = do
    let vs = intersperse "\n" vars
        cs = map bserial constraints
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" ("solve" ∷ vs ∷ cs) ""
    unify hole (lit (string stdOut))
