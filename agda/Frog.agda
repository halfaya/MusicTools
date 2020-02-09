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

-- Frog's song (middle bars)
cfMiddle : Vec Pitch 5
cfMiddle =
  d 5 ∷ e 5 ∷ f 5 ∷ e 5 ∷ d 5 ∷ []

-- First species counterpoint
cpMiddle1 : Vec Interval 5
cpMiddle1 =
  maj6 ∷ min6 ∷ maj3 ∷ min3 ∷ maj6 ∷ []

-- Second species counterpoint (middle bars)
cpMiddle2 : Vec (Interval × Interval) 5
cpMiddle2 =
  -- with dissonant interval
  (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , aug4) ∷
  (min6 , min3) ∷ (min3 , maj6) ∷ []
  -- with unison
  -- (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , per1) ∷
  -- (min3 , min6) ∷ (min3 , maj6) ∷ []

first1 : PitchInterval
first1 = (c 5 , per8)

last1 : PitchInterval
last1 = (c 5 , per8)

middle1 : Vec PitchInterval 5
middle1 = zip cfMiddle cpMiddle1

first2 : PitchInterval
first2 = (c 5 , per5)

middle2 : Vec PitchInterval2 5
middle2 = zip cfMiddle cpMiddle2

last2 : PitchInterval
last2 = (c 5 , per8)

fs : FirstSpecies
fs = firstSpecies first1 (toList middle1) last1 refl refl refl refl

ss : SecondSpecies
ss = secondSpecies first2 (toList middle2) last2 refl refl refl refl refl

cf cp1 cp2 : List Note
cf =
  tone whole (proj₁ (FirstSpecies.firstBar fs)) L∷
  map (tone whole ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  -- yellow highlight when writing
  -- (tone whole ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.firstBar ss)
  tone whole (proj₁ (FirstSpecies.lastBar fs)) L∷
  L[]
  
cp1 =
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.firstBar fs)) L∷
  map (tone whole ∘ proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.lastBar fs)) L∷
  L[]

cp2 =
  rest half L∷
  (tone half ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.firstBar ss))) L∷
  map (tone half ∘ proj₂ ∘ pitchIntervalToPitchPair) (expandPitchIntervals2 (SecondSpecies.middleBars ss)) L++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.lastBar ss)) L∷
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
