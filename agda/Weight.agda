{-# OPTIONS --without-K --allow-exec #-}

module Weight where

open import Prelude hiding (#_)

open import Data.Integer using () renaming (_≤ᵇ_ to _≤ℤ_)
open import Data.Nat  using (_>_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Constraint
open import Counterpoint
open import Exec using (solve)
open import Expr using (evalB; BExpr; IExpr; #_; true) renaming (if_then_else_ to ite)
open import Location
open import MConstraint
open import Music
open import Note
open import Pitch
open import PrettyPrint
open import Symbolic hiding (C; D; E; F; G; A; B)
open import Util using (pairs; filter)
open import Variable

-----------------------------------------------------------
-- Implementation of the functionality of
-- "Weighted Refinement Types for Counterpoint Composition"
-- (Youyou Cong, FARM 2023)
-----------------------------------------------------------

Weight : Type
Weight = ℤ

-- If weight > 0, it is assigned if the constraint is satified; otherwise 0 is assigned
-- If weight < 0, it is assigned if the constraint is not satified; otherwise 0 is assigned
data Weighted (A : Type) : Type where
  weighted : Weight → A → Weighted A

unweight : {A : Type} → Weighted A → A
unweight (weighted _ x) = x

calcWeight : Weighted MConstraint → Weight
calcWeight (weighted n c) =
  if (evalB [] ∘ compileConstraint ∘ mc→c) c
    then (if n ≤ℤ + 0 then + 0 else n)
    else (if n ≤ℤ + 0 then n else + 0)

totalWeight : List (Weighted MConstraint) → Weight
totalWeight = foldl (λ w c → w +ℤ (calcWeight c)) (+ 0)

-∞ : Weight
-∞ = -[1+ 9999 ]

chromaticWeight imperfectWeight contraryWeight repeatedWeight : Weight
chromaticWeight = -[1+ 39 ]
imperfectWeight = + 40
contraryWeight  = + 50
repeatedWeight  = -[1+ 29 ]

imperfectIntervals : List SInt
imperfectIntervals = Min3 ∷ Maj3 ∷ Min6 ∷ Maj6 ∷ []

fsConstraintsVoice : Key → List MPitch → List (Weighted MConstraint)
fsConstraintsVoice k v =
  map (weighted chromaticWeight ∘ scaleConstraint ∘ inScale k) v

-- Expects higher voice first in each pair.
fsConstraints2 : List MP → List (Weighted MConstraint)
fsConstraints2 mp =
  map (weighted -∞ ∘ intervalConstraint ∘ intervalType firstSpeciesIntervals) mp ++
  map (weighted -∞ ∘ intervalConstraint ∘ maxInterval (Int 12)) mp ++
  map (weighted imperfectWeight ∘ intervalConstraint ∘  intervalType imperfectIntervals) mp ++
  map (weighted -∞ ∘ MConstraint.motionConstraint ∘ notDirectIntoPerfect) (pairs mp) ++
  map (weighted contraryWeight ∘ MConstraint.motionConstraint ∘ contrary) (pairs mp)

fsConstraints : Key → [[M]] → List (Weighted MConstraint)
fsConstraints k xss =
  let voiceConstraints = concat (map (fsConstraintsVoice k) xss)
      pairConstraints  = concat (map fsConstraints2 (allPairsPairs xss))
  in voiceConstraints ++ pairConstraints

data HasWeight (f : [[M]] → List (Weighted MConstraint)) (w : Weight) : [[M]] → Type where
  hasWeight : (xss : [[M]]) → totalWeight (f xss) ≡ w → HasWeight f w xss

--------------------------------------------------

C D E F G A B : Octave → SPitch
C = sp C♮ 
D = sp D♮
E = sp E♮
F = sp F♮
G = sp G♮
A = sp A♮
B = sp B♮

Cmaj : Key
Cmaj = key KeyRoot.C major

figure1a figure1b figure1c : Vec (Vec SPitch 5) 2

figure1a =
  (C 5 ∷ G 4 ∷ A 4 ∷ B 4 ∷ C 5 ∷ []) ∷
  (C 4 ∷ E 4 ∷ F 4 ∷ D 4 ∷ C 4 ∷ []) ∷ []

figure1b =
  (C 5 ∷ A 4 ∷ C 5 ∷ B 4 ∷ C 5 ∷ []) ∷
  (C 4 ∷ E 4 ∷ F 4 ∷ D 4 ∷ C 4 ∷ []) ∷ []

figure1c =
  (C 5 ∷ G 4 ∷ sp A♭ 4 ∷ B 4 ∷ C 5 ∷ []) ∷
  (C 4 ∷ E 4 ∷ F 4 ∷ D 4 ∷ C 4 ∷ []) ∷ []

f1 f2 f3 : [[M]]

f1 = toList (vmap (toList ∘ vmap !!) figure1a)
f2 = toList (vmap (toList ∘ vmap !!) figure1b)
f3 = toList (vmap (toList ∘ vmap !!) figure1c)

f1c f2c f3c : List (Weighted MConstraint)
f1c = fsConstraints Cmaj f1
f2c = fsConstraints Cmaj f2
f3c = fsConstraints Cmaj f3

-- show only contraints that are satisfied and have non-negative weight
f1c+ : List (Weighted MConstraint)
f1c+ = filter f1c+f f1c
  where f1c+f : Weighted MConstraint → Bool
        f1c+f (weighted w x) = (+ 0 ≤ℤ w) ∧ (evalB [] ∘ compileConstraint ∘ mc→c) x

f1w f2w f3w : Weight
f1w = totalWeight f1c
f2w = totalWeight f2c
f3w = totalWeight f3c

-- Refinement types are Σ types

{-
f1w=270 : Σ [[M]] (HasWeight (fsConstraints Cmaj) (+ 270))
f1w=270 = f1 , hasWeight f1 refl

f2w=-60 : Σ [[M]] (HasWeight (fsConstraints Cmaj) -[1+ 59 ])
f2w=-60 = f2 , hasWeight f2 refl

f1w=230 : Σ [[M]] (HasWeight (fsConstraints Cmaj) (+ 230))
f1w=230 = f3 , hasWeight f3 refl
-}

--------------------------------------------------

-- Synthesis

compileWeightedConstraint : Weighted MConstraint → IExpr
compileWeightedConstraint (weighted w c) =
  let cond = (compileConstraint ∘ mc→c) c
  in if w ≤ℤ (+ 0)
     then ite cond (# (+ 0)) (# w)
     else ite cond (# w) (# (+ 0))

compileWeightedConstraints : ℤ → List (Weighted MConstraint) → BExpr
compileWeightedConstraints target cs =
  let sum : IExpr
      sum = foldl (λ m n → IExpr._+_ m (compileWeightedConstraint n)) (# (+ 0)) cs
  in BExpr._≥_ sum (# target)

figure1? : [[M]]
figure1? =
  (!! (C 5) ∷ ?? "?1"  ∷ ?? "?2"  ∷ ?? "?3"  ∷ !! (C 5) ∷ []) ∷
  (!! (C 4) ∷ !! (E 4) ∷ !! (F 4) ∷ !! (D 4) ∷ !! (C 4) ∷ []) ∷  []

vars : List String
vars = varNames figure1?

constr : ℤ → BExpr
constr target = compileWeightedConstraints target (fsConstraints Cmaj figure1?)

target : ℤ
target = + 100

-- SMT solution for missing pitches
soln : String
soln = solve vars (constr target ∷ [])

-- solution instantiated into list of all pitches
out : List (List MPitch)
out = instantiatePitches (makeDict vars soln) figure1?

-- pretty printed solution
outp : List String
outp = map (intersperse " " ∘ map showMPitch) out

--------------------------------------------------

-- Two definitions of ℤ⁺

-- not a refinement type
data Pos : Type where
  one  : Pos
  succ : Pos → Pos

-- a refinement of ℕ
ℕ⁺ : Type
ℕ⁺ = Σ ℕ (_> 0)

x1 : ℕ⁺
x1 = 1 , s≤s z≤n
