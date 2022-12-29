{-# OPTIONS --without-K --safe #-}

module Variable where

open import Prelude

open import Location
open import Symbolic

-- Change pitches in the given range to be a varible, named by its location.
makeVar : Range → Located NPitch → Located MPitch
makeVar r (located l x) =
  if l ∈range r
  then located l (?? (showLocation l))
  else located l (!! x)

-- Change all pitches in the given range to be varibles, named by their location.
makeVars1 : Range → List (Located NPitch) → [L]
makeVars1 r xs = map (makeVar r) xs

-- Change all pitches in the given range to be varibles, named by their location.
makeVars : Range → List (List (Located NPitch)) → [[L]]
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
