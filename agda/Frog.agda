{-# OPTIONS --without-K #-}

module Frog where

open import Data.Fin
open import Data.List using (List; map) renaming (_∷_ to _L∷_; _++_ to _L++_; [] to L[])
open import Data.Maybe using (fromMaybe)
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.Vec using (Vec; []; _∷_; zip; toList) renaming (map to vmap)

open import Relation.Binary.PropositionalEquality using (refl)

open import Counterpoint
open import Note
open import Music
open import MidiEvent
open import Pitch
open import Interval
open import Util

-- Frog's song (main body)
cfBody : Vec Pitch 5
cfBody =
  d 5 ∷ e 5 ∷ f 5 ∷ e 5 ∷ d 5 ∷ []

-- First species counterpoint (main body only)
cpBody1 : Vec Interval 5
cpBody1 =
  maj6 ∷ min6 ∷ maj3 ∷ min3 ∷ maj6 ∷ []

-- Second species counterpoint (main body only)
cpBody2 : Vec (Interval × Interval) 5
cpBody2 =
  -- with dissonant interval
  (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , aug4) ∷
  (min6 , min3) ∷ (min3 , maj6) ∷ []
  -- with unison
  -- (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , per1) ∷
  -- (min3 , min6) ∷ (min3 , maj6) ∷ []

cfcp1 : Vec PitchInterval 5
cfcp1 = zip cfBody cpBody1

cfcp2 : Vec PitchInterval2 5
cfcp2 = zip cfBody cpBody2

fs : FirstSpecies
fs = firstSpecies (c 5 , per8) (toList cfcp1) (c 5 , per8) refl refl refl refl

ss : SecondSpecies
ss = secondSpecies (c 5 , per5) (toList cfcp2) (c 5 , per8) refl refl refl refl refl

cf cp1 cp2 : List Note
cf =
  tone half (c 5) L∷
  map (tone half ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  tone half (c 5) L∷
  L[]
  
cp1 =
  tone half (c 6) L∷
  map (tone half ∘ proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  tone half (c 6) L∷
  L[]

cp2 =
  rest qtr L∷
  (tone qtr ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.firstBar ss))) L∷
  -- yellow highlight when writing (tone qtr ∘ proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.firstBar ss)
  map (tone qtr ∘ proj₂ ∘ pitchIntervalToPitchPair) (expandPitchIntervals2 (SecondSpecies.middleBars ss)) L++
  tone half ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.lastBar ss)) L∷
  L[]

----

piano marimba : InstrumentNumber-1
piano   = # 0
marimba = # 12

channel1 channel2 : Channel-1
channel1 = # 0
channel2 = # 1

tempo : ℕ
tempo = 120

cfVelocity cpVelocity : Velocity
cfVelocity = # 60
cpVelocity = # 30

cfTrack : MidiTrack
cfTrack = track "Cantus Firmus" piano channel1 tempo (notes→events cfVelocity cf)

cpTrack1 : MidiTrack
cpTrack1 = track "Counterpoint 1" piano channel2 tempo (notes→events cpVelocity cp1)

cfcpTracks1 : List MidiTrack
cfcpTracks1 = cpTrack1 L∷ cfTrack L∷ L[]

cpTrack2 : MidiTrack
cpTrack2 = track "Counterpoint 2" piano channel2 tempo (notes→events cpVelocity cp2)

cfcpTracks2 : List MidiTrack
cfcpTracks2 = cpTrack2 L∷ cfTrack L∷ L[]
