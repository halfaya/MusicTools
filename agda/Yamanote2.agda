{-# OPTIONS --without-K #-}

module Yamanote2 where

open import Data.Fin
open import Data.Maybe using (fromMaybe)
open import Data.Nat
open import Data.List hiding ([_]; fromMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Counterpoint
open import Note
open import Music renaming (transpose to transposeMusic) hiding (unzip)
open import MidiEvent
open import Pitch
open import ScaleDegree
open import SecondSpecies
open import Util

-- Yamanoto melody transposed down an octave and with an additional d6 at the end.
cantusFirmus : List Pitch
cantusFirmus =
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷
  g 4 ∷ e 4  ∷ g 4 ∷ c 5 ∷ c 5 ∷ c 5 ∷ e 5 ∷ g 5 ∷
  d 6 ∷ c 6 ∷ []

-- Counterpoint by Youyou Cong
counterpoint : List Interval
counterpoint =
  per8 ∷ maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj10 ∷ min6 ∷ per8 ∷ min3 ∷ per8 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ per8 ∷ []
  
-- this one sounds slightly better
counterpoint2 : List Interval
counterpoint2 =
  per8 ∷ maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj3 ∷ min3 ∷ per5 ∷ min6 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ per8 ∷ []

firstSpecies : List PitchInterval
firstSpecies = zip cantusFirmus counterpoint
  
firstSpecies2 : List PitchInterval
firstSpecies2 = zip cantusFirmus counterpoint2

yamanote cp : Music
yamanote = buildMusic pitchToMusic (map (proj₁ ∘ pitchIntervalToPitchPair) firstSpecies2)
cp       = buildMusic pitchToMusic (map (proj₂ ∘ pitchIntervalToPitchPair) firstSpecies2)

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
yamanoteTrack = track "Cantus Firmus" piano channel1 tempo (music→events yVelocity yamanote)

cpTrack : MidiTrack
cpTrack = track "Counterpoint" marimba channel2 tempo (music→events cVelocity cp)

ycpTracks : List MidiTrack
ycpTracks = cpTrack ∷ yamanoteTrack ∷ []
