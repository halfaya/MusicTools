{-# OPTIONS --without-K --safe #-}

module Misc where

open import Prelude

open import Location
open import Symbolic

-- Change pitches in the given range to be a varible, named by its location.
makeVariable : Range → Located NPitch → Located MPitch
makeVariable r (located l x) =
  if l ∈range r
  then located l (?? (showLocation l))
  else located l (!! x)

-- Change all pitches in the given range to be varibles, named by their location.
makeVariables1 : Range → List (Located NPitch) → [L]
makeVariables1 r xs = map (makeVariable r) xs

-- Change all pitches in the given range to be varibles, named by their location.
makeVariables : Range → List (List (Located NPitch)) → [[L]]
makeVariables r xss = map (makeVariables1 r) xss
