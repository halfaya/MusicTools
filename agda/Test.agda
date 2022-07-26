{-# OPTIONS --erased-cubical --safe #-}

module Test where

open import Prelude hiding (#_; _==_; _∨_; _∧_; _-_)

open import Beethoven
open import Constraint
open import Counterpoint
open import Expr
open import Pitch
open import Interval

open import Util using (filter)

test : List Constraint
test = firstSpeciesConstraints remove --beethoven146-1

test2 : List BExpr
test2 = map compileConstraint test

test3 : List Constraint
test3 = filter (not ∘ evalB ∘ compileConstraint) test
