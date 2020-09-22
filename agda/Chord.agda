{-# OPTIONS --cubical --safe #-}

module Chord where

open import Interval
open import Pitch

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Data.Fin        using (Fin; toℕ)
open import Data.List       using (List; map; []; _∷_; _++_; zip)
open import Data.Product    using (_×_)

open import Function        using (_∘_)

allPairs : {A : Type} → List A → List (A × A)
allPairs []       = []
allPairs (x ∷ xs) = map (x ,_) xs ++ allPairs xs

aa = allPairs (c 5 ∷ e 5 ∷ g 5 ∷ [])
bb = zip aa (map (toℕ ∘ unIntervalClass ∘ pitchPairToIntervalClass) aa)

