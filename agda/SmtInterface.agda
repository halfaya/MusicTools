{-# OPTIONS --erased-cubical #-}

module SmtInterface where

open import Prelude hiding (lookup; #_; _+_; _-_)

open import IO.Primitive

open import Constraint using (Constraint; compileConstraint)
open import Counterpoint using (firstSpeciesConstraints; interestingConstraints)
open import Expr renaming (if_then_else_ to i_t_e_)
open import Instruments using (piano)
open import MidiEvent
open import Note
open import Pitch
open import Smt using (HMaybe; just; nothing; HBExpr; B→HBExpr; solveConstraints)

compileConstraints : List Constraint → List HBExpr
compileConstraints = map (B→HBExpr ∘ compileConstraint)

-- Any result which is nonexistant or negative is converted to 0.
HMaybeℤ→Pitch : HMaybe ℤ → Pitch
HMaybeℤ→Pitch nothing           = 0
HMaybeℤ→Pitch (just (+_     n)) = n
HMaybeℤ→Pitch (just (-[1+_] _)) = 0

Dict : Type
Dict = List (String × Pitch)

varDictionary : List String → List (HMaybe ℤ) → Dict
varDictionary xs ys = zip xs (map HMaybeℤ→Pitch ys)

-- Returns 0 if not found.
lookup : Dict → String → Pitch
lookup []             s = 0
lookup ((x , n) ∷ xs) s = if x ==s s then n else lookup xs s

-- Assumes each var name appears only once.
varNames : List (IExpr × IExpr) → List String
varNames []             = []
varNames ((a , b) ∷ xs) = varNamesI a ++ varNamesI b ++ varNames xs

iExpr→Pitch : Dict → IExpr → Pitch
iExpr→Pitch d (# +_ n)      = n
iExpr→Pitch d (# -[1+_] n)  = 0
iExpr→Pitch d (var s)       = lookup d s
iExpr→Pitch d (_ + _)       = 0
iExpr→Pitch d (_ - _)       = 0
iExpr→Pitch d (_ % _)       = 0
iExpr→Pitch d (i _ t _ e _) = 0

firstSpecies→Pitches : List (IExpr × IExpr) → IO (List (Pitch × Pitch))
firstSpecies→Pitches xs = do
  let vnames = varNames xs
      fsc    = firstSpeciesConstraints xs ++ interestingConstraints xs
      cs     = compileConstraints fsc
  res        ← solveConstraints vnames cs
  let f      = iExpr→Pitch (varDictionary vnames res)
  return (map (λ x → f (fst x) , f (snd x)) xs)

firstSpecies→Midi : List (IExpr × IExpr) → IO (List MidiTrack)
firstSpecies→Midi xs = do
  ps      ← firstSpecies→Pitches xs
      -- note that higher MIDI voice is at top, but the input has lower voice first
  let ps1 = map (tone half ∘ snd) ps
      ps2 = map (tone half ∘ fst) ps
      tempo = 240
      tr1 = track "Voice 1" piano channel1 tempo (notes→events defaultVelocity ps1)
      tr2 = track "Voice 2" piano channel2 tempo (notes→events defaultVelocity ps2)
  return (tr1 ∷ tr2 ∷ [])
