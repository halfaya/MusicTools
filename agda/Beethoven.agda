{-# OPTIONS --erased-cubical --safe #-}

module Beethoven where

open import Prelude hiding (#_)

open import Constraint using (P)
open import Counterpoint
open import Expr
open import Pitch
open import Interval
open import Music

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
  (N (g 5) , N (c 6)) ∷
  (N (c 6) , N (e 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (a 5) , N (f 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (N (f 5) , N (c 6)) ∷
  (N (a 5) , N (a 6)) ∷
  (N (c 6) , N (f 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (N (g 5) , N (d 6)) ∷
  (N (g 5) , N (c 6)) ∷ []

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
  (N (g 5) , N (c 6)) ∷
  (N (c 6) , N (e 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (a 5) , N (f 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (N (a 5) , N (c 6)) ∷ -- f5 -> a5
  (N (a 5) , N (a 6)) ∷
  (N (c 6) , N (f 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (N (g 5) , N (d 6)) ∷
  (N (g 5) , N (c 6)) ∷ []

-- Eliminating one note at mistake
beethoven146-1 : List P
beethoven146-1 =
  (N (g 5) , N (c 6)) ∷
  (N (c 6) , N (e 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (a 5) , N (f 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (var "?" , N (c 6)) ∷
  (N (a 5) , N (a 6)) ∷
  (N (c 6) , N (f 6)) ∷
  (N (b 5) , N (g 6)) ∷
  (N (g 5) , N (e 6)) ∷
  (N (g 5) , N (d 6)) ∷
  (N (g 5) , N (c 6)) ∷ []

-- Eliminating three notes at mistake
beethoven146-3 : List P
beethoven146-3 =
  (N (g 5)  , N (c 6)) ∷
  (N (c 6)  , N (e 6)) ∷
  (N (b 5)  , N (g 6)) ∷
  (N (a 5)  , N (f 6)) ∷
  (var "?1" , N (e 6)) ∷
  (var "?2" , N (c 6)) ∷
  (var "?3" , N (a 6)) ∷
  (N (c 6)  , N (f 6)) ∷
  (N (b 5)  , N (g 6)) ∷
  (N (g 5)  , N (e 6)) ∷
  (N (g 5)  , N (d 6)) ∷
  (N (g 5)  , N (c 6)) ∷ []

-- Cantus firmus only, plus start and end of counterpoint
beethoven146cf : List P
beethoven146cf =
  (N (g 5)   , N (c 6)) ∷
  (var "?1"  , N (e 6)) ∷
  (var "?2"  , N (g 6)) ∷
  (var "?3"  , N (f 6)) ∷
  (var "?4"  , N (e 6)) ∷
  (var "?5"  , N (c 6)) ∷
  (var "?6"  , N (a 6)) ∷
  (var "?7"  , N (f 6)) ∷
  (var "?8"  , N (g 6)) ∷
  (var "?9"  , N (e 6)) ∷
  (var "?10" , N (d 6)) ∷
  (N (g 5)   , N (c 6)) ∷ []
