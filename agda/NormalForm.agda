{-# OPTIONS --without-K --safe #-}

module NormalForm where

open import Prelude

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert; empty; show)
open import Util
open import Pitch
open import Interval

-- True iff each element in the first list
-- is ≤ the correspondng element of the second list.
_≤[]_ : List ℕ → List ℕ → Bool
[]       ≤[] ys = true
(x ∷ xs) ≤[] [] = false
(x ∷ xs) ≤[] (y ∷ ys) =
  if x == y
  then xs ≤[] ys
  else (if x <ᵇ y then true else false)

-- True iff each opci between pcs in the first list
-- is ≤ the correspondng opci between pcs in the second list.
_≤[opci]_ : List PC → List PC → Bool
_≤[opci]_ xs ys =
  (map toℕ (pcIntervals xs)) ≤[]
  (map toℕ (pcIntervals ys))

-- Given a list of pc lists, return the pc list that
-- is is smallest under ≤[opci] ordering. The first argument
-- is the current smallest list, normally passed in as [].
bestPitchClassList : List PC → List (List PC) → List PC
bestPitchClassList xs         []         = xs
bestPitchClassList []         (ys ∷ yss) = bestPitchClassList ys yss
bestPitchClassList xs@(_ ∷ _) (ys ∷ yss) =
  if xs ≤[opci] ys
  then bestPitchClassList xs yss
  else bestPitchClassList ys yss

-- Find the normal form of a pc set.
normalForm : PCSet → List PC
normalForm pcs =
  let xs  = fromPCSet pcs
  in bestPitchClassList [] (iter rotateLeft (pred (length xs)) xs)

-- Find the best normal form of a pc set.
-- The best normal form is the smaller of the normal form of the original set
-- and the inverted set under ≤[opci] ordering.
bestNormalForm : PCSet → List PC
bestNormalForm pcs =
  let xs = normalForm pcs
      ys = normalForm (I pcs)
  in if xs ≤[opci] ys then xs else ys

-- Find the prime form of a pc set.
-- The prime form is the best normal form, normalized so that the first pc is 0.
primeForm : PCSet → List PC
primeForm pcs with bestNormalForm pcs
... | []                    = []
... | xs@(p ∷ _) = map (Tp (toℕ (opposite p))) xs

-- Test

ss : Vec PC 4
ss = # 2 ∷ # 0 ∷ # 5 ∷ # 6 ∷ []
--ss = # 4 ∷ # 7 ∷ # 9 ∷ []
--ss = # 8 ∷ # 9 ∷ # 11 ∷ # 0 ∷ # 4 ∷ []
--ss = # 8 ∷ # 7 ∷ # 4 ∷ # 3 ∷ # 11 ∷ # 0 ∷ []

aa = show (toPCSet (toList ss))
bb = map toℕ (fromPCSet (toPCSet (toList ss)))
cc = map toℕ (normalForm (toPCSet (toList ss)))
dd = map toℕ (bestNormalForm (toPCSet (toList ss)))
ee = map toℕ (primeForm (toPCSet (toList ss)))
ff = icVector (primeForm (toPCSet (toList ss)))
gg = map toℕ (fromPCSet (T 8 (toPCSet (toList ss))))

