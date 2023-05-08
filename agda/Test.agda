{-# OPTIONS --without-K --allow-exec #-}

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

inFile : String
inFile = "/Users/leo/Music/XML/Test1.xml"

outFile : String
outFile = "/Users/leo/Music/XML/Test1out.xml"

t1 : String
t1 = readXML inFile

t1n : List (List SNote)
t1n = parseMusic t1

t1p : String
t1p = ppList (ppList showSNote) t1n  -- pretty-printed input

t1m : List (List MPitch)
t1m = map (map SNote.pit) t1n

test : List (Ranged MConstraint)
test = firstSpeciesConstraints (key C major) (indexVoiceBeat t1m)

-- pretty-printed constraints
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

-- pretty-printed constraints failing first-species rules
test5 : List String
test5 = map (showVBBRanged 2 (ppMConstraint [])) test3

---

range : Range
range = rectangle (location 2 2) (location 4 15)

source : List (List (Located MPitch))
source = makeVars range (indexVoiceBeat t1m)

vars : List String
vars = varNames (map (map unlocate) source)

constr : List BExpr
constr = map (compileConstraint ∘ mc→c ∘ unrange) (firstSpeciesConstraints (key C major) source)

x1 : String
x1 = intersperse "\n" vars

x2 : List String
x2 = map bserial constr

-- SMT solution for missing pitches
x3 : String
x3 = solve vars constr

-- solution instantiated into list of all pitches
out : List (List MPitch)
out = instantiatePitchesL (makeDict vars x3) source

outC : List (Ranged MConstraint)
outC = firstSpeciesConstraints (key C major) (indexVoiceBeat out)

-- failed constraints of solution (none)
outF : List (Ranged MConstraint)
outF = filter (not ∘ evalB [] ∘ compileConstraint ∘ mc→c ∘ unrange) outC

-- convert to notes
outN : List (List SNote)
outN = map (map λ p → sn p 8) out

-- list of voices as serialized strings
outS : List String
outS = map (intersperse " " ∘ map showSNote) outN

--outW : String
--outW = writeXML outFile outS
