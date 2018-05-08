module Note where

open import Data.Integer
open import Data.List
open import Data.Product renaming (map to pmap)
open import Function

open import Pitch renaming (transpose to transposePitch)

data Duration : Set where
  duration : ℤ → Duration

data Note : Set where
  note : Duration → Pitch → Note
  rest : Duration         → Note

transpose : ℤ → Note → Note
transpose k (note d p) = note d (transposePitch k p)
transpose k (rest d)   = rest d
