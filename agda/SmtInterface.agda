{-# OPTIONS --erased-cubical #-}

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

compileConstraints : List MConstraint → List HBExpr
compileConstraints = map (B→HBExpr ∘ compileConstraint ∘ mc→c)

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

varNames1 : [P] → List String
varNames1 []             = []
varNames1 (x ∷ xs) = varNamesI x ++ varNames1 xs

varNames : [[P]] → List String
varNames = concatMap varNames1

varNames2 : List P → List String
varNames2 []             = []
varNames2 ((a , b) ∷ xs) = varNamesI a ++ varNamesI b ++ varNames2 xs

iExpr→Pitch : Dict → IExpr → Pitch
iExpr→Pitch d (# +_ n)      = n
iExpr→Pitch d (# -[1+_] n)  = 0
iExpr→Pitch d (var s)       = lookup d s
iExpr→Pitch d (_ + _)       = 0
iExpr→Pitch d (_ - _)       = 0
iExpr→Pitch d (_ % _)       = 0
iExpr→Pitch d (i _ t _ e _) = 0

solvePitches : ([[L]] → List (Ranged MConstraint)) → [[L]] → IO (List (List Pitch))
solvePitches cons nss = do
  let xss    = [[l]]→[[p]] nss
      vnames = varNames xss
      cs     = compileConstraints (map unrange (cons nss))
  res        ← solveConstraints vnames cs
  let f      = iExpr→Pitch (varDictionary vnames res)
  return (map (map f) xss)

solveToMidi : Duration → ([[L]] → List (Ranged MConstraint)) → [[L]] → IO (List MidiTrack)
solveToMidi dur cons nss = do
  pss      ← solvePitches cons nss
  let tempo = 60 * dur -- 240 per note
      ess   = map (notes→events defaultVelocity ∘ (map (tone dur))) pss
  return (events→tracks tempo ess)

solvePitches2 : (List NP → List MConstraint) → List NP → IO (List (Pitch × Pitch))
solvePitches2 cons ns = do
  let xs     = map np→p ns
      vnames = varNames2 xs
      cs     = compileConstraints (cons ns)
  res        ← solveConstraints vnames cs
  let f      = iExpr→Pitch (varDictionary vnames res)
  return (map (λ x → f (fst x) , f (snd x)) xs)

solveToMidi2 : Duration → (List NP → List MConstraint) → List NP → IO (List MidiTrack)
solveToMidi2 dur cons ns = do
  ps      ← solvePitches2 cons ns
  let ps1 = map (tone dur ∘ fst) ps
      ps2 = map (tone dur ∘ snd) ps
      tempo = 60 * dur -- 240 per note
      tr1 = track "Voice 1" piano channel1 tempo (notes→events defaultVelocity ps1)
      tr2 = track "Voice 2" piano channel2 tempo (notes→events defaultVelocity ps2)
  return (tr1 ∷ tr2 ∷ [])
