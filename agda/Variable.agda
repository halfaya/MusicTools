{-# OPTIONS --without-K --safe #-}

module Variable where

open import Prelude

open import Expr     using (Dict)
open import Location
open import Pitch    using (Pitch)
open import Symbolic

-- Change pitches in the given range to be a varible, named by its location.
makeVar : Range → Located SPitch → Located MPitch
makeVar r (located l x) =
  if l ∈range r
  then located l (?? (showLocation l))
  else located l (!! x)

-- Change all pitches in the given range to be varibles, named by their location.
makeVars1 : Range → List (Located SPitch) → [L]
makeVars1 r xs = map (makeVar r) xs

-- Change all pitches in the given range to be varibles, named by their location.
makeVars : Range → List (List (Located SPitch)) → [[L]]
makeVars r xss = map (makeVars1 r) xss

varNames1 : [M] → List String
varNames1 []          = []
varNames1 (!! x ∷ xs) = varNames1 xs
varNames1 (?? x ∷ xs) = x ∷ varNames1 xs

varNames : [[M]] → List String
varNames = concatMap varNames1

varNames2 : List MP → List String
varNames2 []             = []
varNames2 ((a , b) ∷ xs) = varNames1 (a ∷ []) ++ varNames1 (b ∷ []) ++ varNames2 xs

--------

instantiatePitches : Dict → [[M]] → List (List SPitch)
instantiatePitches d = map (map (mp→np d))

instantiatePitchesL : Dict → [[L]] → List (List SPitch)
instantiatePitchesL d = map (map (mp→np d ∘ unlocate))

--------

-- Second argument is space separated list of integers.
-- Any integer ≤ 0 is converted to 0.
-- Assumes number of variables and values are equal.
makeDict : List String → String → Dict
makeDict vs s =
  let f : String → ℤ
      f s = + (fromMaybe 0 (readMaybe 10 s))
  in zip vs (map f (words s))
