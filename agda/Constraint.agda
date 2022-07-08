{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Cubical.Core.Everything using (Type)

open import Data.List using (List)

data SetConstraint (A : Type) :  Type where
  inSet : A → (List A) → SetConstraint A
