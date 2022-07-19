{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Prelude

open import Util using (_∈_via_)

data SetConstraint (A : Type) :  Type where
  inSet : (List A) → SetConstraint A

checkSetConstraint : {A : Type} → (A → A → Bool) → SetConstraint A → A → Bool
checkSetConstraint f (inSet xs) x = x ∈ xs via f

data IExpr : Type where
  const : ℤ → IExpr
  var   : String → IExpr

data BExpr : Type where
  eq : IExpr → IExpr → BExpr
