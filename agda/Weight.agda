{-# OPTIONS --without-K --safe #-}

module Weight where

open import Prelude

open import Data.Integer renaming (_≤ᵇ_ to _≤ℤ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Constraint
open import Counterpoint
open import Expr using (evalB)
open import Location
open import MConstraint
open import Music
open import Note
open import Pitch
open import PrettyPrint
open import Symbolic hiding (C; D; E; F; G; A; B)
open import Util using (pairs; filter)

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
-∞ = -[1+ 99 ]

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
  map (weighted -∞ ∘ intervalConstraint ∘  intervalType firstSpeciesIntervals) mp ++
  map (weighted imperfectWeight ∘ intervalConstraint ∘  intervalType imperfectIntervals) mp ++
  map (weighted -∞ ∘ MConstraint.motionConstraint ∘ notDirectIntoPerfect) (pairs mp) ++
  map (weighted contraryWeight ∘ MConstraint.motionConstraint ∘ contrary) (pairs mp)

fsConstraints : Key → [[M]] → List (Weighted MConstraint)
fsConstraints k xss =
  let voiceConstraints = concat (map (fsConstraintsVoice k) xss)
      pairConstraints  = concat (map fsConstraints2 (allPairsPairs xss))
  in voiceConstraints ++ pairConstraints

data HasWeight (f : [[M]] → List (Weighted MConstraint)) (xss : [[M]]) (w : Weight) : Type where
  hasWeight : totalWeight (f xss) ≡ w → HasWeight f xss w

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

f1w=270 : HasWeight (fsConstraints Cmaj) f1 (+ 270)
f1w=270 = hasWeight refl

-- fix the contraints
W : [[M]] → Weight → Type
W = HasWeight (fsConstraints Cmaj)

f2w=-60 : W f2 (-[1+ 59 ])
f2w=-60 = hasWeight refl

f1w=230 : W f3 (+ 230)
f1w=230 = hasWeight refl
