{-# OPTIONS --without-K #-}

module Yamanote where

open import Data.Fin
open import Data.List using (List; map) renaming (_∷_ to _L∷_; [] to L[])
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
open import ScaleDegree
open import Util

-- Yamanoto melody transposed down an octave and with an additional d6 at the end.
cantusFirmus : Vec Pitch 42
cantusFirmus =
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 4 ∷ e 4  ∷ g 4 ∷ c 5 ∷ c 5 ∷ c 5 ∷ e 5 ∷ g 5 ∷
  d 6 ∷ c 6 ∷ []

-- Counterpoint by Youyou Cong
counterpoint : Vec Interval 42
counterpoint =
  per8 ∷ maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj10 ∷ min6 ∷ per8 ∷ min3 ∷ per8 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ per8 ∷ []
  
-- this one sounds slightly better
counterpoint2 : Vec Interval 42
counterpoint2 =
  per8 ∷ maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj3 ∷ min3 ∷ per5 ∷ min6 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ per8 ∷ []

firstSpecies : Vec PitchInterval 42
firstSpecies = zip cantusFirmus counterpoint

isFS1 : IsFirstSpecies (toList firstSpecies)
isFS1 = refl
  
firstSpecies2 : Vec PitchInterval 42
firstSpecies2 = zip cantusFirmus counterpoint2

isFS2 : IsFirstSpecies (toList firstSpecies2)
isFS2 = refl

yamanote counterp : List Note
yamanote = map (tone 8th ∘ proj₁ ∘ pitchIntervalToPitchPair) (toList firstSpecies2)
counterp = map (tone 8th ∘ proj₂ ∘ pitchIntervalToPitchPair) (toList firstSpecies2)

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

