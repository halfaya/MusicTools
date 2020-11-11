{-# OPTIONS --cubical --safe #-}

module Chord where

open import Interval
open import Pitch

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Data.Fin        using (Fin; toℕ) renaming (zero to fz)
open import Data.List       using (List; map; []; _∷_; _++_; zip)
open import Data.Nat        using (ℕ)
open import Data.Product    using (_×_)

open import Function        using (_∘_)

open import AssocList
open import BitVec
open import Pitch
open import Util            using (_+N_)

data Root : Type where
  root : Fin chromaticScaleSize → Root

data Quality : Type where
  Maj : Quality
  Min : Quality

RootQuality : Type
RootQuality = Root × Quality

Notes : Type
Notes = BitVec chromaticScaleSize

makeChord : Root → List ℕ → Notes
makeChord (root n) []       = BitVec.insert n empty
makeChord (root n) (x ∷ xs) = BitVec.insert (n +N x) (makeChord (root n) xs)

majorTriad : Root → Notes
majorTriad r = makeChord r (4 ∷ 7 ∷ [])

aa = show (majorTriad (root fz))

{-
allPairs : {A : Type} → List A → List (A × A)
allPairs []       = []
allPairs (x ∷ xs) = map (x ,_) xs ++ allPairs xs

aa = allPairs (c 5 ∷ e 5 ∷ g 5 ∷ [])
bb = zip aa (map (toℕ ∘ unIntervalClass ∘ pitchPairToIntervalClass) aa)
-}
