{-# OPTIONS --without-K  --allow-exec #-}

module Test where

open import Prelude hiding (#_; _==_; _∨_; _∧_; _-_; _+_; if_then_else_; _≤_)

open import Beethoven hiding (C; D; E; F; G; A; B)
open import Constraint
open import Exec
open import Kennan hiding (C; D; E; F; G; A; B)
open import MConstraint
open import Counterpoint
open import Expr
open import Location
open import Parse
open import PrettyPrint
open import Serial
open import Symbolic
open import Tanaka hiding (C; D; E; F; G; A; B)
open import Variable

open import Util

fileName : String
fileName = "/Users/leo/Downloads/XML/Test 1.xml"

t1 : String
t1 = readFile fileName

t1n = parseMusic t1
t1m = map (map !!) t1n
t1p = ppList (ppList showNPitch) t1n

test : List (Ranged MConstraint)
test = firstSpeciesConstraints (key C major) (indexVoiceBeat t1m)

test1 : List String
test1 = map (showRanged (ppMConstraint [])) test

test2 : List BExpr
test2 = map (compileConstraint ∘ mc→c ∘ unrange) test

test2a : List String
test2a = map bserial test2

test3 : List (Ranged MConstraint)
test3 = filter (not ∘ evalB [] ∘ compileConstraint ∘ mc→c ∘ unrange) test

test4 : List String
test4 = map (showRanged (ppMConstraint [])) test3

test5 : List String
test5 = map (showVBBRanged 2 (ppMConstraint [])) test3

test6 : List (List (Located MPitch))
test6 = makeVars (rectangle (location 2 2) (location 4 11))
                 (indexVoiceBeat beethoven146)

---

range   = rectangle (location 2 2) (location 4 11)
source  = makeVars range (indexVoiceBeat (take 3 beethoven146))
vars    = varNames (map (map unlocate) source)
cons    = map (compileConstraint ∘ mc→c ∘ unrange) (defaultConstraints source)

x1 = intersperse "\n" vars
x2 = map bserial cons

b1 = solve vars cons
b2 = instantiatePitchesL (makeDict vars b1) source
b3 = map (intersperse " " ∘ map showNPitch) b2
