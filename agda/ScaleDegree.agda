{-# OPTIONS --cubical --safe #-}

module ScaleDegree where

open import Prelude

open import Pitch

ScaleDegree : ℕ → Set
ScaleDegree = Fin

ScaleDegreeOctave : ℕ → Set
ScaleDegreeOctave n = ScaleDegree n × Octave

transposeScaleDegree : {n : ℕ} → ℕ → ScaleDegreeOctave (suc n) → ScaleDegreeOctave (suc n)
transposeScaleDegree {n} k (d , o) =
  let d' = (toℕ d) + k
  in d' mod (suc n) , o + (d' div (suc n))

scaleDegreeToPC : {n : ℕ} → Scale n → ScaleDegree n → PC
scaleDegreeToPC scale d = lookup scale d

