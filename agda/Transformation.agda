{-# OPTIONS --without-K --safe #-}

module Transformation where

open import Prelude

open import Note         using (Note; tone; rest)
open import Pitch        using (Pitch; transposePitch)
open import Interval     using (PitchPair)

retrograde : List Note → List Note
retrograde = reverse

-- Create a list of intervals between all adjacent tones, ignoring rests.
intervals : List Note → List ℤ
intervals [] = []
intervals (rest _ ∷ ns) = intervals ns
intervals (tone d p ∷ ns) = intervals' p ns where
  intervals' : Pitch → List Note → List ℤ
  intervals' p []                              = []
  intervals' p (rest d ∷ ns)                   = intervals' p ns
  intervals' p (tone d q ∷ ns) = (+ q) - (+ p) ∷ intervals' q ns

inversion : List Note → List Note
inversion []                 = []
inversion    (rest d   ∷ ns) = rest d   ∷ inversion ns
inversion xs@(tone d p ∷ ns) = tone d p ∷ inversion' p is ns where
  is : List ℤ
  is = map (-_) (intervals xs)

  inversion' : Pitch → List ℤ → List Note → List Note
  inversion' p []         ns              = ns
  inversion' _ (_ ∷ _)    []              = []
  inversion' p is@(_ ∷ _) (rest d ∷ ns)   = rest d ∷ inversion' p is ns
  inversion' p (i ∷ is)   (tone d _ ∷ ns) = let q = transposePitch i p in (tone d q) ∷ inversion' q is ns
