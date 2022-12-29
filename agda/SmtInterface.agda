{-# OPTIONS --without-K #-}

module SmtInterface where

open import Prelude hiding (lookup; #_; _+_; _-_)

open import IO.Primitive

open import Constraint
open import Counterpoint
open import Expr renaming (if_then_else_ to i_t_e_)
open import Instruments using (piano)
open import Location
open import MConstraint
open import MidiEvent
open import Note
open import Pitch
open import Util using (_divℕ_)
open import Smt using (HMaybe; just; nothing; HBExpr; B→HBExpr; solveConstraints)
open import Symbolic
open import Variable

compileConstraints : List MConstraint → List HBExpr
compileConstraints = map (B→HBExpr ∘ compileConstraint ∘ mc→c)

fromHMaybe : {A : Type} → A → HMaybe A → A
fromHMaybe default nothing  = default
fromHMaybe _       (just x) = x

varDictionary : List String → List (HMaybe ℤ) → Dict
varDictionary xs ys = zip xs (map (fromHMaybe (+ 0)) ys)

solvePitches : ([[L]] → List (Ranged MConstraint)) → [[L]] → IO (List (List Pitch))
solvePitches cons lss = do
  let mss    = [[l]]→[[m]] lss
      vnames = varNames mss
      cs     = compileConstraints (map unrange (cons lss))
  res        ← solveConstraints vnames cs
  let f      = name→pitch (varDictionary vnames res)
  return (map (map f) mss)

solveToMidi : Duration → ([[L]] → List (Ranged MConstraint)) → [[L]] → IO (List MidiTrack)
solveToMidi dur cons lss = do
  pss      ← solvePitches cons lss
  let tempo = 60 * dur -- 240 per note
      ess   = map (notes→events defaultVelocity ∘ (map (tone dur))) pss
  return (events→tracks tempo ess)

solvePitches2 : (List MP → List MConstraint) → List MP → IO (List (Pitch × Pitch))
solvePitches2 cons ms = do
  let vnames = varNames2 ms
      cs     = compileConstraints (cons ms)
  res        ← solveConstraints vnames cs
  let f      = name→pitch (varDictionary vnames res)
  return (map (λ x → f (fst x) , f (snd x)) ms)

solveToMidi2 : Duration → (List MP → List MConstraint) → List MP → IO (List MidiTrack)
solveToMidi2 dur cons ms = do
  ps      ← solvePitches2 cons ms
  let ps1 = map (tone dur ∘ fst) ps
      ps2 = map (tone dur ∘ snd) ps
      tempo = 60 * dur -- 240 per note
      tr1 = track "Voice 1" piano channel1 tempo (notes→events defaultVelocity ps1)
      tr2 = track "Voice 2" piano channel2 tempo (notes→events defaultVelocity ps2)
  return (tr1 ∷ tr2 ∷ [])

