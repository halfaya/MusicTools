{-# OPTIONS --without-K --safe #-}

module ScaleDegree where

open import Data.Fin        using (Fin; toℕ; #_)
open import Data.Nat        using (ℕ; suc; _+_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_)
open import Data.Vec        using (lookup)

open import Pitch

data ScaleDegree (n : ℕ) : Set where
  scaleDegree : Fin n → ScaleDegree n

ScaleDegreeOctave : ℕ → Set
ScaleDegreeOctave n = ScaleDegree n × Octave

transposeScaleDegree : {n : ℕ} → ℕ → ScaleDegreeOctave (suc n) → ScaleDegreeOctave (suc n)
transposeScaleDegree {n} k (scaleDegree d , octave o) =
  let d' = (toℕ d) + k
  in scaleDegree (d' mod (suc n)) , octave (o + (d' div (suc n)))

scaleDegreeToPitchClass : {n : ℕ} → Scale n → ScaleDegree n → PitchClass
scaleDegreeToPitchClass scale (scaleDegree d) = lookup scale d

