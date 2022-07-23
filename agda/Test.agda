{-# OPTIONS --erased-cubical --safe #-}

module Test where

open import Prelude

open import Beethoven
open import Constraint
open import Counterpoint
open import Expr
open import Pitch
open import Interval

open import Util using (filter; _∘_)

test : List SetConstraint
test = firstSpeciesConstraints (unMaybe beethoven146a)

test2 : List BExpr
test2 = map compileSetConstraint test

test3 : List SetConstraint
test3 = filter (not ∘ evalB ∘ compileSetConstraint) test
