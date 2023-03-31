{-# OPTIONS --without-K --safe #-}

module Kennan where

open import Prelude

open import Pitch using (Octave)
open import Symbolic hiding (C; D; E; F; G; A; B)

C D E F G A B : Octave → SPitch
C = sp C♮ 
D = sp D♮
E = sp E♮
F = sp F♮
G = sp G♮
A = sp A♮
B = sp B♮

-- Workbook page 2, number 1
k2-1 : List (SPitch × SPitch)
k2-1 =
   (C 4 , C 6) ∷
   (D 4 , B 5) ∷
   (E 4 , C 6) ∷
   (F 4 , A 5) ∷
   (F 4 , D 6) ∷
   (G 4 , B 5) ∷
   (C 4 , C 6) ∷ []

-- Workbook page 2, number 2
k2-2 : List (SPitch × SPitch)
k2-2 =
   (C 4 , C 6) ∷
   (E 4 , B 5) ∷
   (C 4 , C 6) ∷
   (G 4 , D 6) ∷
   (C 5 , E 6) ∷ []
