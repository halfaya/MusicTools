{-# OPTIONS --erased-cubical --safe #-}

module Beethoven where

open import Prelude

open import Symbolic

-- Example 146 (page 29, number 2) in Beethoven Werke XIII
beethoven146 : List (NPitch × NPitch)
beethoven146 =
   (G 5 , C 6) ∷
   (C 6 , E 6) ∷
   (B 5 , G 6) ∷
   (A 5 , F 6) ∷
   (G 5 , E 6) ∷
   (F 5 , C 6) ∷
   (A 5 , A 6) ∷
   (C 6 , F 6) ∷
   (B 5 , G 6) ∷
   (G 5 , E 6) ∷
   (G 5 , D 6) ∷
   (G 5 , C 6) ∷ []

-- Haydn's correction
beethoven146h : List (NPitch × NPitch)
beethoven146h =
   (G 5 , C 6) ∷
   (C 6 , E 6) ∷
   (B 5 , G 6) ∷
   (A 5 , F 6) ∷
   (G 5 , E 6) ∷
   (A 5 , C 6) ∷ -- f5 -> a5
   (A 5 , A 6) ∷
   (C 6 , F 6) ∷
   (B 5 , G 6) ∷
   (G 5 , E 6) ∷
   (G 5 , D 6) ∷
   (G 5 , C 6) ∷ []

-- Eliminating one note at mistake
beethoven146-1 : List (NPitch × NPitch)
beethoven146-1 =
   (G 5    , C 6) ∷
   (C 6    , E 6) ∷
   (B 5    , G 6) ∷
   (A 5    , F 6) ∷
   (G 5    , E 6) ∷
   (?? "?" , C 6) ∷
   (A 5    , A 6) ∷
   (C 6    , F 6) ∷
   (B 5    , G 6) ∷
   (G 5    , E 6) ∷
   (G 5    , D 6) ∷
   (G 5    , C 6) ∷ []

-- Eliminating three notes at mistake
beethoven146-3 : List (NPitch × NPitch)
beethoven146-3 =
   (G 5     , C 6) ∷
   (C 6     , E 6) ∷
   (B 5     , G 6) ∷
   (A 5     , F 6) ∷
   (?? "?1" , E 6) ∷
   (?? "?2" , C 6) ∷
   (?? "?3" , A 6) ∷
   (C 6     , F 6) ∷
   (B 5     , G 6) ∷
   (G 5     , E 6) ∷
   (G 5     , D 6) ∷
   (G 5     , C 6) ∷ []

-- Cantus firmus only, plus start and end of counterpoint
beethoven146cf : List (NPitch × NPitch)
beethoven146cf =
   (G 5      , C 6) ∷
   (?? "?1"  , E 6) ∷
   (?? "?2"  , G 6) ∷
   (?? "?3"  , F 6) ∷
   (?? "?4"  , E 6) ∷
   (?? "?5"  , C 6) ∷
   (?? "?6"  , A 6) ∷
   (?? "?7"  , F 6) ∷
   (?? "?8"  , G 6) ∷
   (?? "?9"  , E 6) ∷
   (?? "?10" , D 6) ∷
   (G 5      , C 6) ∷ []
