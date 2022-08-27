{-# OPTIONS --erased-cubical #-}

module Test where

open import Prelude hiding (#_; _==_; _∨_; _∧_; _-_; _+_; if_then_else_)

open import Beethoven
open import Constraint
open import MConstraint
open import Counterpoint
open import Expr
open import Pitch
open import PrettyPrint
open import Interval
open import Smt
open import SmtInterface
open import Symbolic

open import Util using (filter)

test : List MConstraint
test = firstSpeciesConstraints (key C major) beethoven146h

test1 : List String
test1 = map ppMConstraint test

test2 : List BExpr
test2 = map (compileConstraint ∘ mc→c) test

--test3 : List HBExpr
--test3 = compileConstraints test

test4 : List MConstraint
test4 = filter (not ∘ evalB ∘ compileConstraint ∘ mc→c) test

test5 : List String
test5 = map ppMConstraint test4
