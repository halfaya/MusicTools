{-# OPTIONS --without-K #-}

module OldSpecies where

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

motionOk : (i1 : PitchInterval) (i2 : PitchInterval) → Set
motionOk i1 i2 with motion (pitchIntervalToPitchPair i1) (pitchIntervalToPitchPair i2) | isPerfect (proj₂ i2)
motionOk i1 i2 | contrary | _     = ⊤
motionOk i1 i2 | oblique  | _     = ⊤
motionOk i1 i2 | parallel | false = ⊤
motionOk i1 i2 | parallel | true  = ⊥
motionOk i1 i2 | similar  | false = ⊤
motionOk i1 i2 | similar  | true  = ⊥

-- interval in index is initial interval
-- final interval of a cadence is (p , per 8)
data FirstSpecies :  PitchInterval → Set where
  cadence2 : (p : Pitch) → FirstSpecies (transpose (+ 2) p    , maj6)
  cadence7 : (p : Pitch) → FirstSpecies (transpose -[1+ 0 ] p , min10)
  _∷_ : (pi : PitchInterval){_ : (T ∘ isConsonant ∘ proj₂) pi}
        {pj : PitchInterval}{_ : (T ∘ isConsonant ∘ proj₂) pj} →
        {_ : motionOk pi pj} → FirstSpecies pj → FirstSpecies pi

firstSpeciesToMusic : {pi : PitchInterval} → FirstSpecies pi → Music
firstSpeciesToMusic {pi} (cadence2 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic {pi} (cadence7 p) = pitchIntervalToMusic pi ∷ pitchIntervalToMusic (p , per8)
firstSpeciesToMusic      (pi ∷ fs)    = pitchIntervalToMusic pi ∷ firstSpeciesToMusic fs

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
pitchPairToMusic2 (p , q) (r , s) = (note (tone 16th p) ∥ note (tone 16th q)) ∷ (note (tone 16th r) ∥ note (tone 16th s))

pitchIntervalToMusic2 : PitchInterval → Interval → Music
pitchIntervalToMusic2 (p , i) j = pitchPairToMusic2 (pitchIntervalToPitchPair (p , i)) (pitchIntervalToPitchPair (p , j))

secondSpeciesToMusic : {pi : PitchInterval} → SecondSpecies pi → Music
secondSpeciesToMusic {pi} (cadence2 p)     = pitchIntervalToMusic2 pi maj6 ∷ pitchIntervalToMusic (p , per8)
secondSpeciesToMusic      ([ pi / i ]∷ fs) = pitchIntervalToMusic2 pi i ∷ secondSpeciesToMusic fs

