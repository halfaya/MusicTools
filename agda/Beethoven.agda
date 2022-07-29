{-# OPTIONS --erased-cubical --safe #-}

module Beethoven where

open import Prelude hiding (#_)

open import Constraint using (P)
open import Counterpoint
open import Expr
open import Pitch
open import Interval
open import Music

n : Pitch → IExpr
n = #_ ∘ +_

-- Example 146 (page 29, number 2) in Beethoven Werke XIII
beethoven146 : List (Pitch × Pitch)
beethoven146 =
   (g 5 , c 6) ∷
   (c 6 , e 6) ∷
   (b 5 , g 6) ∷
   (a 5 , f 6) ∷
   (g 5 , e 6) ∷
   (f 5 , c 6) ∷
   (a 5 , a 6) ∷
   (c 6 , f 6) ∷
   (b 5 , g 6) ∷
   (g 5 , e 6) ∷
   (g 5 , d 6) ∷
   (g 5 , c 6) ∷ []

beethoven146a : List P
beethoven146a =
  (n (g 5) , n (c 6)) ∷
  (n (c 6) , n (e 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (a 5) , n (f 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (n (f 5) , n (c 6)) ∷
  (n (a 5) , n (a 6)) ∷
  (n (c 6) , n (f 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (n (g 5) , n (d 6)) ∷
  (n (g 5) , n (c 6)) ∷ []

{-
beethoven146a2 : FirstSpecies2 (Maybe PSym)
beethoven146a2 = FirstSpecies2
  (just (G Na, 5) , just (C Na, 6)) ∷
  (just (C Na, 6) , just (E Na, 6)) ∷
  (just (B Na, 5) , just (G Na, 6)) ∷
  (just (A Na, 5) , just (F Na, 6)) ∷
  (just (G Na, 5) , just (E Na, 6)) ∷
  (just (F Na, 5) , just (C Na, 6)) ∷
  (just (A Na, 5) , just (A Na, 6)) ∷
  (just (C Na, 6) , just (F Na, 6)) ∷
  (just (B Na, 5) , just (G Na, 6)) ∷
  (just (G Na, 5) , just (E Na, 6)) ∷
  (just (G Na, 5) , just (D Na, 6)) ∷
  (just (G Na, 5) , just (C Na, 6)) ∷ []
-}

-- Haydn's correction
beethoven146h : List P
beethoven146h =
  (n (g 5) , n (c 6)) ∷
  (n (c 6) , n (e 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (a 5) , n (f 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (n (a 5) , n (c 6)) ∷ -- f5 -> a5
  (n (a 5) , n (a 6)) ∷
  (n (c 6) , n (f 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (n (g 5) , n (d 6)) ∷
  (n (g 5) , n (c 6)) ∷ []

-- Eliminating one note at mistake
beethoven146-1 : List P
beethoven146-1 =
  (n (g 5) , n (c 6)) ∷
  (n (c 6) , n (e 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (a 5) , n (f 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (var "?" , n (c 6)) ∷
  (n (a 5) , n (a 6)) ∷
  (n (c 6) , n (f 6)) ∷
  (n (b 5) , n (g 6)) ∷
  (n (g 5) , n (e 6)) ∷
  (n (g 5) , n (d 6)) ∷
  (n (g 5) , n (c 6)) ∷ []

-- Eliminating three notes at mistake
beethoven146-3 : List P
beethoven146-3 =
  (n (g 5)  , n (c 6)) ∷
  (n (c 6)  , n (e 6)) ∷
  (n (b 5)  , n (g 6)) ∷
  (n (a 5)  , n (f 6)) ∷
  (var "?1" , n (e 6)) ∷
  (var "?2" , n (c 6)) ∷
  (var "?3" , n (a 6)) ∷
  (n (c 6)  , n (f 6)) ∷
  (n (b 5)  , n (g 6)) ∷
  (n (g 5)  , n (e 6)) ∷
  (n (g 5)  , n (d 6)) ∷
  (n (g 5)  , n (c 6)) ∷ []

-- Cantus firmus only, plus start and end of counterpoint
beethoven146cf : List P
beethoven146cf =
  (n (g 5)   , n (c 6)) ∷
  (var "?1"  , n (e 6)) ∷
  (var "?2"  , n (g 6)) ∷
  (var "?3"  , n (f 6)) ∷
  (var "?4"  , n (e 6)) ∷
  (var "?5"  , n (c 6)) ∷
  (var "?6"  , n (a 6)) ∷
  (var "?7"  , n (f 6)) ∷
  (var "?8"  , n (g 6)) ∷
  (var "?9"  , n (e 6)) ∷
  (var "?10" , n (d 6)) ∷
  (n (g 5)   , n (c 6)) ∷ []
