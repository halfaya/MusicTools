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
  -- returns the contents of a MusicXML file as serialized music
  readXML : String → Term → TC ⊤
  readXML file hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" ("readXML" ∷ file ∷ []) ""
    unify hole (lit (string stdOut))

  -- converts serialized music (list of voices) to MusicXML and writes the result to a file
  writeXML : String → List String → Term → TC ⊤
  writeXML file voices hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" ("writeXML" ∷ file ∷ voices) ""
    unify hole (lit (string stdOut))

  -- vars is a list of variable names
  -- returns a space-separated list of integer values for each variable
  solve : List String → List BExpr → Term → TC ⊤
  solve vars constraints hole = do
    let vs = intersperse "\n" vars
        cs = map bserial constraints
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" ("solve" ∷ vs ∷ cs) ""
    unify hole (lit (string stdOut))
