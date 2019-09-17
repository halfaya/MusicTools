{-# OPTIONS --without-K #-}

module SecondSpecies where

open import Music hiding (transpose)
open import Note hiding (transpose)
open import Pitch
open import Counterpoint

open import Data.Bool hiding (_≟_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_;  -[1+_])
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- NOTE: Not yet the exact conditions for second species.
-- interval in index is initial interval
-- final interval of a cadence is (p , per 8)
data SecondSpecies :  PitchInterval → Set where
  cadence2 : (p : Pitch) → SecondSpecies (transpose (+ 2) p    , per5)
--  cadence7 : (p : Pitch) → SecondSpecies (transpose -[1+ 0 ] p , min10)
  [_/_]∷_ : (pi : PitchInterval){_ : (T ∘ isConsonant ∘ proj₂) pi}
            (i2 : Interval){_ : (T ∘ isConsonant) i2} →
            {pj : PitchInterval}{_ : (T ∘ isConsonant ∘ proj₂) pj} →
            {_ : motionOk (proj₁ pi , i2) pj} → {_ : motionOk pi pj} →
            SecondSpecies pj → SecondSpecies pi

pitchPairToMusic2 : PitchPair → PitchPair → Music
pitchPairToMusic2 (p , q) (r , s) = (note (note 16th p) ∥ note (note 16th q)) ∷ (note (note 16th r) ∥ note (note 16th s))

pitchIntervalToMusic2 : PitchInterval → Interval → Music
pitchIntervalToMusic2 (p , i) j = pitchPairToMusic2 (pitchIntervalToPitchPair (p , i)) (pitchIntervalToPitchPair (p , j))

secondSpeciesToMusic : {pi : PitchInterval} → SecondSpecies pi → Music
secondSpeciesToMusic {pi} (cadence2 p)     = pitchIntervalToMusic2 pi maj6 ∷ pitchIntervalToMusic (p , per8)
secondSpeciesToMusic      ([ pi / i ]∷ fs) = pitchIntervalToMusic2 pi i ∷ secondSpeciesToMusic fs

