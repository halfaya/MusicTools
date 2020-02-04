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

-- Frog's song
cantusFirmus : Vec Pitch 7
cantusFirmus =
  c 5 ∷ d 5 ∷ e 5 ∷ f 5 ∷ e 5 ∷ d 5 ∷ c 5 ∷ []

-- Main body only
cantusFirmusBody : Vec Pitch 5
cantusFirmusBody =
  d 5 ∷ e 5 ∷ f 5 ∷ e 5 ∷ d 5 ∷ []

-- First species counterpoint 
counterpoint1 : Vec Interval 7
counterpoint1 =
  per8 ∷ maj6 ∷ min6 ∷ maj3 ∷ min3 ∷ maj6 ∷ per8 ∷ []

-- Second species counterpoint (main body only)
counterpoint2 : Vec (Interval × Interval) 5
counterpoint2 = 
  (min3 , per5) ∷ (min3 , min6) ∷ (maj3 , aug4) ∷
  (min6 , min3) ∷ (min3 , maj6) ∷ []

zipped1 : Vec PitchInterval 7
zipped1 = zip cantusFirmus counterpoint1

zipped2 : Vec PitchInterval2 5
zipped2 = zip cantusFirmusBody counterpoint2

fs : FirstSpecies
fs = firstSpecies (toList zipped1) refl refl refl refl refl

-- This should type check! Something is wrong with checkWeakBeats?
ss : SecondSpecies
ss = secondSpecies (c 5 , per5) (toList zipped2) (c 5 , per8) refl refl refl refl refl refl

frog counterp1 counterp2 : List Note
frog = map (tone half ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.notes fs)
counterp1 = map (tone half ∘ proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.notes fs)
counterp2 =
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

fVelocity cVelocity : Velocity
fVelocity = # 60
cVelocity = # 30

frogTrack : MidiTrack
frogTrack = track "Cantus Firmus" piano channel1 tempo (notes→events fVelocity frog)

cpTrack1 : MidiTrack
cpTrack1 = track "Counterpoint 1" piano channel2 tempo (notes→events cVelocity counterp1)

fcpTracks1 : List MidiTrack
fcpTracks1 = cpTrack1 L∷ frogTrack L∷ L[]

cpTrack2 : MidiTrack
cpTrack2 = track "Counterpoint 2" piano channel2 tempo (notes→events cVelocity counterp2)

fcpTracks2 : List MidiTrack
fcpTracks2 = cpTrack2 L∷ frogTrack L∷ L[]
