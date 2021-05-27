{-# OPTIONS --cubical --safe #-}

module ScaleDegree where

open import Data.Fin        using (Fin; toℕ; #_)
open import Data.Nat        using (ℕ; suc; _+_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_)
open import Data.Vec        using (lookup)

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

