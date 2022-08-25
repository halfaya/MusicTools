{-# OPTIONS --erased-cubical #-}

module Test where

open import Prelude hiding (#_; _==_; _∨_; _∧_; _-_; _+_; if_then_else_)

open import Beethoven
open import Constraint
open import HConstraint
open import Counterpoint
open import Expr
open import Key
open import Pitch
open import PrettyPrint
open import Interval
open import Smt
open import SmtInterface
open import Symbolic

open import Util using (filter)

test : List HConstraint
test = firstSpeciesConstraints  beethoven146

test2 : List BExpr
test2 = map (compileConstraint ∘ hc→c) test

--test3 : List HBExpr
--test3 = compileConstraints test

test4 : List HConstraint
test4 = filter (not ∘ evalB ∘ compileConstraint ∘ hc→c) test

test5 : List String
test5 = map ppHConstraint test4
