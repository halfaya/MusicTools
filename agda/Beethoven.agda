{-# OPTIONS --without-K --safe #-}

module Beethoven where

open import Prelude

open import Music
open import Note
open import Pitch using (Octave)
open import Symbolic hiding (C; D; E; F; G; A; B)

C D E F G A B : Octave → NPitch
C = np C♮ 
D = np D♮
E = np E♮
F = np F♮
G = np G♮
A = np A♮
B = np B♮

-- Example 146 (page 29, number 2) in Beethoven Werke XIII
beethoven146v : Vec (Vec NPitch 12) 4
beethoven146v =
  (C 5 ∷ E 5 ∷ G 5 ∷ F 5 ∷ E 5 ∷ C 5 ∷ A 5 ∷ F 5 ∷ G 5 ∷ E 5 ∷ D 5 ∷ C 5 ∷ []) ∷
  (G 4 ∷ C 5 ∷ B 4 ∷ A 4 ∷ G 4 ∷ F 4 ∷ A 4 ∷ C 5 ∷ B 4 ∷ G 4 ∷ G 4 ∷ G 4 ∷ []) ∷
  (E 4 ∷ C 4 ∷ D 4 ∷ D 4 ∷ B 3 ∷ A 3 ∷ C 4 ∷ C 4 ∷ D 4 ∷ C 4 ∷ B 3 ∷ C 4 ∷ []) ∷
  (C 4 ∷ A 3 ∷ G 3 ∷ D 3 ∷ E 3 ∷ F 3 ∷ F 3 ∷ A 3 ∷ G 3 ∷ C 4 ∷ G 3 ∷ C 3 ∷ []) ∷ []

beethoven146 : List (List NPitch)
beethoven146 = toList (vmap toList beethoven146v)

beethoven146m : List (List MPitch)
beethoven146m = map (map !!) beethoven146

--beethoven146c : Counterpoint 4 (12 * half)
--beethoven146c = cp (vmap (pitches→melody half ∘ vmap (mp→p [])) beethoven146v)

-- Example 146 (page 29, number 2) in Beethoven Werke XIII
-- Soprano and Alto voice only
beethoven146sa : List (NPitch × NPitch)
beethoven146sa =
   (G 4 , C 5) ∷
   (C 5 , E 5) ∷
   (B 4 , G 5) ∷
   (A 4 , F 5) ∷
   (G 4 , E 5) ∷
   (F 4 , C 5) ∷
   (A 4 , A 5) ∷
   (C 5 , F 5) ∷
   (B 4 , G 5) ∷
   (G 4 , E 5) ∷
   (G 4 , D 5) ∷
   (G 4 , C 5) ∷ []

-- Haydn's correction
beethoven146h : List (NPitch × NPitch)
beethoven146h =
   (G 4 , C 5) ∷
   (C 5 , E 5) ∷
   (B 4 , G 5) ∷
   (A 4 , F 5) ∷
   (G 4 , E 5) ∷
   (A 4 , C 5) ∷ -- f4 -> a4
   (A 4 , A 5) ∷
   (C 5 , F 5) ∷
   (B 4 , G 5) ∷
   (G 4 , E 5) ∷
   (G 4 , D 5) ∷
   (G 4 , C 5) ∷ []

{-
-- Eliminating one note at mistake
beethoven146-1 : List (NPitch × NPitch)
beethoven146-1 =
   (G 4    , C 5) ∷
   (C 5    , E 5) ∷
   (B 4    , G 5) ∷
   (A 4    , F 5) ∷
   (G 4    , E 5) ∷
   (?? "?" , C 5) ∷
   (A 4    , A 5) ∷
   (C 5    , F 5) ∷
   (B 4    , G 5) ∷
   (G 4    , E 5) ∷
   (G 4    , D 5) ∷
   (G 4    , C 5) ∷ []

-- Eliminating three notes at mistake
beethoven146-3 : List (NPitch × NPitch)
beethoven146-3 =
   (G 4     , C 5) ∷
   (C 5     , E 5) ∷
   (B 4     , G 5) ∷
   (A 4     , F 5) ∷
   (?? "?1" , E 5) ∷
   (?? "?2" , C 5) ∷
   (?? "?3" , A 5) ∷
   (C 5     , F 5) ∷
   (B 4     , G 5) ∷
   (G 4     , E 5) ∷
   (G 4     , D 5) ∷
   (G 4     , C 5) ∷ []

-- Cantus firmus only, plus start and end of counterpoint
beethoven146cf : List (NPitch × NPitch)
beethoven146cf =
   (G 4      , C 5) ∷
   (?? "?1"  , E 5) ∷
   (?? "?2"  , G 5) ∷
   (?? "?3"  , F 5) ∷
   (?? "?4"  , E 5) ∷
   (?? "?5"  , C 5) ∷
   (?? "?5"  , A 5) ∷
   (?? "?7"  , F 5) ∷
   (?? "?8"  , G 5) ∷
   (?? "?9"  , E 5) ∷
   (?? "?10" , D 5) ∷
   (G 4      , C 5) ∷ []
-}
