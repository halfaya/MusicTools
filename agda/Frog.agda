{-# OPTIONS --without-K #-}

module Frog where

open import Data.Fin
open import Data.List using (List; []; _∷_; _++_; zip; map)
open import Data.Maybe using (fromMaybe)
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Counterpoint
open import Note
open import Music
open import MidiEvent
open import Pitch
open import Interval
open import Util

-- Frog's song (middle bars)
cfMiddle : List Pitch 
cfMiddle =
  d 5 ∷ e 5 ∷ f 5 ∷ e 5 ∷ d 5 ∷ []

-- First species counterpoint
cpMiddle1 : List Interval 
cpMiddle1 =
  maj6 ∷ min6 ∷ maj3 ∷ min3 ∷ maj6 ∷ []

-- Second species counterpoint (middle bars)
cpMiddle2 : List (Interval × Interval) 
cpMiddle2 =
  -- with dissonant interval and unison
  (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , aug4) ∷
  (min6 , per1) ∷ (min3 , maj6) ∷ []
  -- with dissonant interval
  -- (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , aug4) ∷
  -- (min6 , min3) ∷ (min3 , maj6) ∷ []
  -- with unison
  -- (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , per1) ∷
  -- (min3 , min6) ∷ (min3 , maj6) ∷ []

first1 : PitchInterval
first1 = (c 5 , per8)

last1 : PitchInterval
last1 = (c 5 , per8)

middle1 : List PitchInterval 
middle1 = zip cfMiddle cpMiddle1

first2 : PitchInterval
first2 = (c 5 , per5)

middle2 : List PitchInterval2 
middle2 = zip cfMiddle cpMiddle2

last2 : PitchInterval
last2 = (c 5 , per8)

fs : FirstSpecies
fs = firstSpecies first1 middle1 last1 refl refl refl refl

ss : SecondSpecies
ss = secondSpecies first2 middle2 last2 refl refl refl refl refl

cf cp1 cp2 : List Note
cf =
  tone whole (proj₁ (FirstSpecies.firstBar fs)) ∷
  map (tone whole ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) ++
  -- yellow highlight when writing
  -- (tone whole ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.firstBar ss)
  tone whole (proj₁ (FirstSpecies.lastBar fs)) ∷
  []
  
cp1 =
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.firstBar fs)) ∷
  map (tone whole ∘ proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) ++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.lastBar fs)) ∷
  []

cp2 =
  rest half ∷
  (tone half ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.firstBar ss))) ∷
  map (tone half ∘ proj₂ ∘ pitchIntervalToPitchPair) (expandPitchIntervals2 (SecondSpecies.middleBars ss)) ++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.lastBar ss)) ∷
  []

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
cfcpTracks1 = cpTrack1 ∷ cfTrack ∷ []

cpTrack2 : MidiTrack
cpTrack2 = track "Counterpoint 2" piano channel2 tempo (notes→events cpVelocity cp2)

cfcpTracks2 : List MidiTrack
cfcpTracks2 = cpTrack2 ∷ cfTrack ∷ []
