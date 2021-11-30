{-# OPTIONS --cubical #-}

-- First and second species counterpoint for Frog's song
module Frog where

open import Data.Fin
open import Data.List using (List; []; _∷_; _++_; map)
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
open import Util hiding (_∘_)

-- First species counterpoint (musical content)
first : PitchInterval
first = (c 5 , per8)

middle : List PitchInterval 
middle = (d 5 , maj6) ∷ (e 5 , min6) ∷ (f 5 , maj3) ∷ (e 5 , min3) ∷ (d 5 , maj6) ∷ []

middle' : List PitchInterval 
middle' = (d 5 , per8) ∷ (e 5 , min6) ∷ (f 5 , maj3) ∷ (e 5 , min3) ∷ (d 5 , maj6) ∷ []

last : PitchInterval
last = (c 5 , per8)

-- Second species counterpoint (musical content)
first2 : PitchInterval
first2 = (c 5 , per5)

middle2 : List PitchInterval2 
middle2 = (d 5 , min3 , per5) ∷ (e 5 , min3 , min6) ∷ (f 5 , maj3 , aug4) ∷
          (e 5 , min6 , per1) ∷ (d 5 , min3 , maj6) ∷ []

last2 : PitchInterval
last2 = (c 5 , per8)

-- Correct first species counterpoint
fs : FirstSpecies
fs = firstSpecies first middle last refl refl refl refl

{-
-- Parallel octave example from Section 3.3; ill-typed
fs' : FirstSpecies
fs' = firstSpecies first middle' last refl refl refl refl
-}

-- Correct second species counterpoint
ss : SecondSpecies
ss = secondSpecies first2 middle2 last2 refl refl refl refl refl


-- Music as list of notes
cf cp1 cp2 : List Note
cf =
  tone whole (proj₁ (FirstSpecies.firstBar fs)) ∷
  map (tone whole ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) ++
  tone whole (proj₁ (FirstSpecies.lastBar fs)) ∷
  []
  
cp1 =
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.firstBar fs)) ∷
  map (λ x → tone whole (secondPitch x)) (FirstSpecies.middleBars fs) ++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.lastBar fs)) ∷
  []

cp2 =
  rest half ∷
  (tone half ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.firstBar ss))) ∷
  map (λ x → tone half (secondPitch x)) (expandPitchIntervals2 (SecondSpecies.middleBars ss)) ++
  tone whole ((proj₂ ∘ pitchIntervalToPitchPair) (SecondSpecies.lastBar ss)) ∷
  []

----

-- MIDI generation
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
