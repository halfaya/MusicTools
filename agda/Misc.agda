{-# OPTIONS --without-K --safe #-}

module Misc where

open import Prelude

open import Location
open import Symbolic

-- Change pitches in the given range to be a varible, named by its location.
makeVariable : Range → Located NPitch → Located NPitch
makeVariable r x@(located l _) =
  if l ∈range r
  then located l (?? (showLocation l))
  else x

-- Change all pitches in the given range to be varibles, named by their location.
makeVariables1 : Range → [L] → [L]
makeVariables1 r xs = map (makeVariable r) xs

-- Change all pitches in the given range to be varibles, named by their location.
makeVariables : Range → [[L]] → [[L]]
makeVariables r xss = map (makeVariables1 r) xss
