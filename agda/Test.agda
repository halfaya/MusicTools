{-# OPTIONS --erased-cubical --safe #-}

module Test where

open import Prelude hiding (#_; _==_; _∨_; _∧_; _-_; _+_; if_then_else_)

open import Beethoven
open import Constraint
open import Kennan
open import MConstraint
open import Counterpoint
open import Expr
open import Location
open import PrettyPrint
open import Symbolic
open import Tanaka

open import Util


test : List (Ranged MConstraint)
--test = firstSpeciesConstraints (key C major) tanaka1 --beethoven146
--test = firstSpeciesConstraints (key C major) (index2VoiceBeat k2-2)
test = firstSpeciesConstraints (key C major) (indexVoiceBeat beethoven146)

test1 : List String
test1 = map (showRanged ppMConstraint) test

test2 : List BExpr
test2 = map (compileConstraint ∘ mc→c ∘ unrange) test

test3 : List (Ranged MConstraint)
test3 = filter (not ∘ evalB ∘ compileConstraint ∘ mc→c ∘ unrange) test

test4 : List String
test4 = map (showRanged ppMConstraint) test3

test5 : List String
test5 = map (showRanged ppMConstraint ∘ mapRange (toVBBrange 2)) test3
