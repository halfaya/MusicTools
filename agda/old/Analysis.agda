{-# OPTIONS --cubical --safe #-}

module Analysis where

open import Data.List       using (List; []; _∷_; map)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Harmony
open import Music
open import Note
open import Pitch

-- test of analysis

accompF : List Pitch
accompF = f 4 ∷ a 4 ∷ c 5 ∷ []

xx = pitchClassListToSet (map pitchToClass accompF)
--yy = showPitchClassSet xx

zz : xx ≡ IV-maj
zz = refl
