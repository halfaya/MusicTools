{-# OPTIONS --cubical --safe #-}

module Yamanote where

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
-- open import ScaleDegree
open import Util

-- Yamanoto melody transposed down an octave and with an additional d6 at the end.
cantusFirmus : Vec Pitch 40
cantusFirmus =
        g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 4 ∷ e 4  ∷ g 4 ∷ c 5 ∷ c 5 ∷ c 5 ∷ e 5 ∷ g 5 ∷
  d 6 ∷ []

-- Counterpoint (composed on Aug 2, 2019)
counterpoint : Vec Upi 40
counterpoint =
         maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj3 ∷ min3 ∷ per5 ∷ min6 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ []

-- Counterpoint (composed on March 18, 2019)
counterpoint0 : Vec Upi 40
counterpoint0 =
         maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj10 ∷ min6 ∷ per8 ∷ min3 ∷ per8 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ []

yamanote-cfcp : Vec PitchInterval 40
yamanote-cfcp = zip cantusFirmus counterpoint

fs : FirstSpecies
fs = firstSpecies (g 5 , per8) (toList yamanote-cfcp) (c 6 , per8) refl refl refl refl

yamanote counterp : List Note
yamanote =
  tone 8th (g 5) L∷
  map (tone 8th ∘ proj₁ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  tone 8th (g 5) L∷
  L[]
  
counterp =
  tone 8th (g 6) L∷
  map (tone 8th ∘ proj₂ ∘ pitchIntervalToPitchPair) (FirstSpecies.middleBars fs) L++
  tone 8th (c 7) L∷
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

yVelocity cVelocity : Velocity
yVelocity = # 60
cVelocity = # 30

yamanoteTrack : MidiTrack
yamanoteTrack = track "Cantus Firmus" piano channel1 tempo (notes→events yVelocity yamanote)

cpTrack : MidiTrack
cpTrack = track "Counterpoint" marimba channel2 tempo (notes→events cVelocity counterp)

ycpTracks : List MidiTrack
ycpTracks = cpTrack L∷ yamanoteTrack L∷ L[]

