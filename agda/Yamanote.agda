{-# OPTIONS --without-K #-}

module Yamanote where


open import Pitch
open import Counterpoint
open import Note
open import Music        renaming (transpose to transposeMusic)
open import MidiEvent
open import ScaleDegree
open import Util

open import Data.Fin
open import Data.Maybe using (fromMaybe)
open import Data.Nat
open import Data.List hiding ([_]; fromMaybe; unzip)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Yamanoto melody transposed down an octave and with an additional d6 at the end.
cantusFirmus : List Pitch
cantusFirmus =
  g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷
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

firstSpecies : FirstSpecies (g 5 , per8)
firstSpecies = 
  (g 5 , per8) ∷ (g 4 , maj6) ∷ (a 4 , min6) ∷ (g 4 , per8) ∷ (c 5 , maj3) ∷ (g 4 , per8) ∷ (e 5 , min3) ∷ (g 4 , maj6) ∷
  (g 5 , maj6) ∷ (g 4 , maj6) ∷ (a 4 , min3) ∷ (g 4 , per5) ∷ (c 5 , maj3) ∷ (g 4 , maj6) ∷ (e 5 , min3) ∷ (g 4 , per8) ∷
  (g 5 , maj3) ∷ (g 4 , maj10) ∷ (a 4 , per8) ∷ (g 4 , maj10) ∷ (b 4 , min6) ∷ (g 4 , per8) ∷ (d 5 , maj6) ∷ (g 4 , maj10) ∷
  (g 5 , maj3) ∷ (g 4 , maj10) ∷ (a 4 , min6) ∷ (g 4 , per8) ∷ (b 4 , min3) ∷ (g 4 , per8) ∷ (d 5 , min3) ∷ (g 4 , per8) ∷
  (g 4 , maj6) ∷ (e 4 , min10) ∷ (g 4 , per8) ∷ (c 5 , maj10) ∷ (c 5 , per8) ∷ (c 5 , maj10) ∷ (e 5 , min10) ∷ (g 5 , per8) ∷
  (cadence2 (c 6))
  
firstSpecies2 : FirstSpecies (g 5 , per8)
firstSpecies2 = 
  (g 5 , per8) ∷ (g 4 , maj6) ∷ (a 4 , min6) ∷ (g 4 , per8) ∷ (c 5 , maj3) ∷ (g 4 , per8) ∷ (e 5 , min3) ∷ (g 4 , maj6) ∷
  (g 5 , maj6) ∷ (g 4 , maj6) ∷ (a 4 , min3) ∷ (g 4 , per5) ∷ (c 5 , maj3) ∷ (g 4 , maj6) ∷ (e 5 , min3) ∷ (g 4 , per8) ∷
  (g 5 , maj3) ∷ (g 4 , maj10) ∷ (a 4 , per8) ∷ (g 4 , maj10) ∷ (b 4 , min6) ∷ (g 4 , per8) ∷ (d 5 , maj6) ∷ (g 4 , maj10) ∷
  (g 5 , maj3) ∷ (g 4 , maj3) ∷ (a 4 , min3) ∷ (g 4 , per5) ∷ (b 4 , min6) ∷ (g 4 , maj6) ∷ (d 5 , min3) ∷ (g 4 , per8) ∷
  (g 4 , maj6) ∷ (e 4 , min10) ∷ (g 4 , per8) ∷ (c 5 , maj10) ∷ (c 5 , per8) ∷ (c 5 , maj10) ∷ (e 5 , min10) ∷ (g 5 , per8) ∷
  (cadence2 (c 6))

farm : FirstSpecies (g 4 , per8)
farm = 
  (g 4 , per8) ∷ (c 5 , maj10) ∷ (c 5 , per8) ∷ (c 5 , maj10) ∷ (e 5 , min10) ∷ (g 5 , per8) ∷
  (cadence2 (c 6))

exercise : Music × Music
exercise = unzip (firstSpeciesToMusic firstSpecies2)

yamanote cp : Music
yamanote = proj₁ exercise
cp       = proj₂ exercise

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
