{-# OPTIONS --without-K  --allow-exec #-}

module Exec where

open import Reflection using (TC; Term; _>>=_; unify; lit; string)

open import Prelude

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
           → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}

-- You must add /bin/cat to ~/.agda/executables to run this.
macro
  readFile : String → Term → TC ⊤ -- returns the contents of the file as a String
  readFile file hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "HMusicTools" (file ∷ []) ""
    unify hole (lit (string stdOut))
