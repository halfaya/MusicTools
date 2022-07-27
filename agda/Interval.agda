{-# OPTIONS --erased-cubical --safe #-}

module Interval where

open import Prelude

open import Pitch
open import Util using (allPairs; ◯pairs; firstPairs)

-- Maximum number of interval classes (0 to 6).
ic7 : ℕ
ic7 = 7

PitchPair : Type
PitchPair = Pitch × Pitch

PCPair : Type
PCPair = PC × PC

-- Unordered pitch interval
-- Absolute distance in semitones between two pitches.
Upi : Type
Upi = ℕ

-- Ordered pitch interval
-- Relative distance in semitones between two pitches.
Opi : Type
Opi = ℤ

-- Interval Class
-- Also known as unodered pitch-class interval (upci).
IC : Type
IC = Fin ic7

-- (Ordered) pitch-class interval (also abbreviated opci)
PCI : Type
PCI = Fin s12

intervalWithinOctave : Upi → Upi
intervalWithinOctave i = toℕ (i mod s12)

absoluteInterval : Opi → Upi
absoluteInterval i = ∣ i ∣

makeSigned : Sign → Upi → Opi
makeSigned Sign.- zero    = + 0
makeSigned Sign.- (suc i) = -[1+ i ]
makeSigned Sign.+ i       = + i

-- Names for intervals
per1  = 0
min2  = 1
maj2  = 2
min3  = 3
maj3  = 4
per4  = 5
aug4  = 6
per5  = 7
min6  = 8
maj6  = 9
min7  = 10
maj7  = 11
per8  = 12
min9  = 13
maj9  = 14
min10 = 15
maj10 = 16
per11 = 17
aug11 = 18
per12 = 19

isConsonant : Upi → Bool
isConsonant iv =
  (i == per1)  ∨
  (i == min3)  ∨
  (i == maj3)  ∨
  (i == per5)  ∨
  (i == min6)  ∨
  (i == maj6)  ∨
  (i == per8)
  where i = intervalWithinOctave iv

isDissonant : Upi → Bool
isDissonant = not ∘ isConsonant

isPerfect : Upi → Bool
isPerfect iv =
  (i == per1)  ∨
  (i == per4)  ∨
  (i == per5)  ∨
  (i == per8)
  where i = intervalWithinOctave iv

isUnison : Upi → Bool
isUnison i = i == per1

isThird : Upi → Bool
isThird i = (i == min3) ∨ (i == maj3)

-- Half or whole step.
isStep : Upi → Bool
isStep i =
  (i == min2)  ∨
  (i == maj2)

PitchInterval : Type
PitchInterval = Pitch × Upi

pitchIntervalToPitchPair : PitchInterval → PitchPair
pitchIntervalToPitchPair (p , n) = (p , transposePitch (+ n)  p)

secondPitch : PitchInterval → Pitch
secondPitch = snd ∘ pitchIntervalToPitchPair

pitchPairToOpi : PitchPair → Opi
pitchPairToOpi (p , q) = (+ q) - (+ p)

toIC : PCPair → IC
toIC (p , q) =
  let x = toℕ (∣ (+ (toℕ q)) - (+ (toℕ p)) ∣ mod s12)
  in x ⊓ (s12 ∸ x) mod ic7

toPCI : PCPair → PCI
toPCI (p , q) =
 (((+ (toℕ q)) - (+ (toℕ p))) modℕ s12) mod s12

-- Assumes p ≤ q
toPitchInterval : PitchPair → PitchInterval
toPitchInterval pq = fst pq , absoluteInterval (pitchPairToOpi pq)

-- DEPRECATED? Note that the first and last pitches are compared in normal order, not circular order.
◯pcIntervals : List PC → List PCI
◯pcIntervals = map toPCI ∘ ◯pairs

-- Note that the first and last pitches are compared in normal order, not circular order.
pcIntervals : List PC → List PCI
pcIntervals = map toPCI ∘ reverse ∘ firstPairs

stepUp : Pitch → Pitch → Bool
stepUp p q with pitchPairToOpi (p , q)
... | +_     n = isStep n
... | -[1+_] n = false

stepDown : Pitch → Pitch → Bool
stepDown p q with pitchPairToOpi (p , q)
... | +_     n = false
... | -[1+_] n = isStep n

-- Check if q is a passing tone between p and r
-- The interval between end points need to be a 3rd
isPassingTone : Pitch → Pitch → Pitch → Bool
isPassingTone p q r =
  (stepUp p q ∧ stepUp q r) ∨ (stepDown p q ∧ stepDown q r) ∨
  (isThird (absoluteInterval (pitchPairToOpi (p , r))))

moveUp : Pitch → Pitch → Bool
moveUp p q with pitchPairToOpi (p , q)
... | +_     _ = true
... | -[1+_] _ = false

moveDown : Pitch → Pitch → Bool
moveDown p q = not (moveUp p q)

-- Check if q is left by step in the opposite direction from its approach
isOppositeStep : Pitch → Pitch → Pitch → Bool
isOppositeStep p q r = (moveUp p q ∧ stepDown q r) ∨ (moveDown p q ∧ stepUp q r)

transposePitchInterval : Opi → Pitch → Pitch
transposePitchInterval z p = transposePitch z p

-- transpose pitch class by pci
Tpci : PCI → PC → PC
Tpci n = Tp (toℕ n)

----------

-- Interval Class Vector
ICV : Type
ICV = Vec ℕ ic7

emptyICV : ICV
emptyICV = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

icVector : List PC → ICV
icVector pcs =
  foldl
    (λ icv pc → updateAt (toIC pc) suc icv)
    (updateAt (# 0) (λ _ → length pcs) emptyICV)
    (allPairs pcs)

----------

--Construct matrix out of PC row
matrix : List PC → List (List PC)
matrix [] = []
matrix pcs@(pc ∷ _) =
  let r0 = map ((Tpci ∘ Ip) pc) pcs -- start first row at 0
  in map (λ p → map ((Tpci ∘ Ip) p) r0) r0

showMatrix : List (List PC) → String
showMatrix m = intersperse "\n" (map showPCs m)

{-
rr : List PC
rr = # 10 ∷ # 9 ∷ # 7 ∷ # 0 ∷ []
rp = rr ++ map (Tp 4) rr ++ map (Tp 8) rr

-- Belle's matrix
aa = showMatrix (matrix rp)


0 b 9 2 4 3 1 6 8 7 5 a
1 0 a 3 5 4 2 7 9 8 6 b
3 2 0 5 7 6 4 9 b a 8 1
a 9 7 0 2 1 b 4 6 5 3 8
8 7 5 a 0 b 9 2 4 3 1 6
9 8 6 b 1 0 a 3 5 4 2 7
b a 8 1 3 2 0 5 7 6 4 9
6 5 3 8 a 9 7 0 2 1 b 4
4 3 1 6 8 7 5 a 0 b 9 2
5 4 2 7 9 8 6 b 1 0 a 3
7 6 4 9 b a 8 1 3 2 0 5
2 1 b 4 6 5 3 8 a 9 7 0


rd : List PC
rd2 = reverse (map (Tp 4) rr)
rd3' = reverse (map (Tp 8) rr)
rd3 = reverse (take 2 rd3') ++ reverse (drop 2 rd3')
rd = rr ++ rd2 ++ rd3

-- Dan's matrix
ad = showMatrix (matrix rd)


0 b 9 2 6 1 3 4 5 a 8 7
1 0 a 3 7 2 4 5 6 b 9 8
3 2 0 5 9 4 6 7 8 1 b a
a 9 7 0 4 b 1 2 3 8 6 5
6 5 3 8 0 7 9 a b 4 2 1
b a 8 1 5 0 2 3 4 9 7 6
9 8 6 b 3 a 0 1 2 7 5 4
8 7 5 a 2 9 b 0 1 6 4 3
7 6 4 9 1 8 a b 0 5 3 2
2 1 b 4 8 3 5 6 7 0 a 9
4 3 1 6 a 5 7 8 9 2 0 b
5 4 2 7 b 6 8 9 a 3 1 0
-}
