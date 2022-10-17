{-# OPTIONS --erased-cubical --safe #-}

module Kennan where

open import Prelude

open import Symbolic

-- Workbook page 2, number 1
k2-1 : List (NPitch × NPitch)
k2-1 =
   (C 4 , C 6) ∷
   (D 4 , B 5) ∷
   (E 4 , C 6) ∷
   (F 4 , A 5) ∷
   (F 4 , D 6) ∷
   (G 4 , B 5) ∷
   (C 4 , C 6) ∷ []

-- Workbook page 2, number 2
k2-2 : List (NPitch × NPitch)
k2-2 =
   (C 4 , C 6) ∷
   (E 4 , B 5) ∷
   (C 4 , C 6) ∷
   (G 4 , D 6) ∷
   (C 5 , E 6) ∷ []
