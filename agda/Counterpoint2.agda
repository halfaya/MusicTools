{-# OPTIONS --without-K #-}

module Counterpoint2 where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_; not)
open import Data.Fin using (Fin; #_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; mapMaybe; map; zip; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_; _≡ᵇ_; _<ᵇ_; compare; _∸_; ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec using ([]; _∷_; Vec; lookup; drop; reverse)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Counterpoint
open import Music
open import Note
open import Pitch
open import Interval hiding (PitchInterval2)
open import Util using (pairs)

----------------------------------
-- Potential alternative representation for second-species counterpoint.

PitchInterval2 : Set
PitchInterval2 = Pitch × Interval × Interval

strongBeat : PitchInterval2 → PitchInterval
strongBeat (p , i , _) = p , i

weakBeat : PitchInterval2 → PitchInterval
weakBeat (p , _ , i) = p , i

-- We might want to lift the ordinary interval error to one involving PitchInterval2
-- to give the user more context, but for now keep it simple.

checkStrongBeats : List PitchInterval2 → List IntervalError
checkStrongBeats = checkIntervals ∘ map strongBeat

checkWeakBeat : PitchInterval2 → Pitch → Maybe IntervalError
checkWeakBeat (p , i , j) q =
  if isPassingNote (secondPitch (p , i)) (secondPitch (p , j)) q
  then nothing
  else intervalCheck j

checkWeakBeats : List PitchInterval2 → Pitch → List IntervalError
checkWeakBeats []            p = []
checkWeakBeats pis@(_ ∷ qis) p =
  mapMaybe (uncurry checkWeakBeat) (zip pis (map proj₁ qis ++ (p ∷ [])))
