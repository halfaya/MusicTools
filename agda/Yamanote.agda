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
open import Data.List hiding ([_]; fromMaybe)
open import Data.List.NonEmpty using (List⁺; fromList; [_])
open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality hiding ([_])

bar1 bar3 bar5 cantusFirmus : List Pitch

bar1 = g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ c 5 ∷ g 4 ∷ e 5 ∷ g 4 ∷ []
bar3 = g 5 ∷ g 4  ∷ a 4 ∷ g 4 ∷ b 4 ∷ g 4 ∷ d 5 ∷ g 4 ∷ []
bar5 = g 4 ∷ e 4  ∷ g 4 ∷ c 5 ∷ c 5 ∷ c 5 ∷ e 5 ∷ g 5 ∷ []
coda = d 6 ∷ c 6 ∷ []

cantusFirmus = bar1 ++ bar1 ++ bar3 ++ bar3 ++ bar5 ++ coda

counterpoint : List IntervalQuality
counterpoint =
  per8 ∷ maj6 ∷ min6 ∷ per8 ∷ maj3 ∷ per8 ∷ min3 ∷ maj6 ∷
  maj6 ∷ maj6 ∷ min3 ∷ per5 ∷ maj3 ∷ maj6 ∷ min3 ∷ per8 ∷
  maj3 ∷ maj10 ∷ per8 ∷ maj10 ∷ min6 ∷ per8 ∷ maj6 ∷ maj10 ∷
  maj3 ∷ maj10 ∷ min6 ∷ per8 ∷ min3 ∷ per8 ∷ min3 ∷ per8 ∷
  maj6 ∷ min10 ∷ per8 ∷ maj10 ∷ per8 ∷ maj10 ∷ min10 ∷ per8 ∷
  maj6 ∷ per8 ∷ []

twoLines : List PitchInterval
twoLines = zip cantusFirmus counterpoint

twoLines⁺ : List⁺ PitchInterval
twoLines⁺ = fromMaybe [ c 5 , per5 ] (fromList twoLines)

firstSpecies : FirstSpecies twoLines⁺
firstSpecies =
  i (pitch 67 , per8) (other refl) (i (pitch 55 , maj6) (other refl) (i (pitch 57 , min6) (contrary refl)
  (i (pitch 55 , per8) (other refl) (i (pitch 60 , maj3) (contrary refl) (i (pitch 55 , per8) (other refl)
  (i (pitch 64 , min3) (other refl) (i (pitch 55 , maj6) (other refl)
  (i (pitch 67 , maj6) (other refl) (i (pitch 55 , maj6) (other refl) (i (pitch 57 , min3) (contrary refl)
  (i (pitch 55 , per5) (other refl) (i (pitch 60 , maj3) (other refl) (i (pitch 55 , maj6) (other refl)
  (i (pitch 64 , min3) (oblique refl)  (i (pitch 55 , per8) (other refl)
  (i (pitch 67 , maj3) (other refl) (i (pitch 55 , maj10) (contrary refl) (i (pitch 57 , per8) (other refl)
  (i (pitch 55 , maj10) (other refl) (i (pitch 59 , min6) (oblique refl) (i (pitch 55 , per8) (other refl)
  (i ((pitch 62) , maj6) (other refl) (i (pitch 55 , maj10) (other refl)
  (i (pitch 67 , maj3) (other refl) (i (pitch 55 , maj10) (other refl) (i (pitch 57 , min6) (contrary refl)
  (i (pitch 55 , per8) (other refl) (i (pitch 59 , min3) (contrary refl) (i (pitch 55 , per8) (other refl)
  (i (pitch 62 , min3) (contrary refl) (i (pitch 55 , per8) (other refl) (i (pitch 55 , maj6) (other refl)
  (i (pitch 52 , min10) (oblique refl) (i (pitch 55 , per8) (other refl)
  (i (pitch 60 , maj10) (oblique refl) (i (pitch 60 , per8) (other refl) (i (pitch 60 , maj10) (other refl)
  (i (pitch 64 , min10) (oblique refl) (i (pitch 67 , per8) (other refl) (cadence2 (pitch 72)))))))))))))))))))))))))))))))))))))))))

yamanote ycp : Music
yamanote  = fromNotes (map (note 8th) cantusFirmus)
ycp       = firstSpeciesToMusic firstSpecies

----

instrument : InstrumentNumber-1
instrument = # 0 -- piano

channel : Channel-1
channel = # 0

tempo : ℕ
tempo = 180

yamanoteTrack : List MidiTrack
yamanoteTrack = track "Piano" instrument channel tempo (music→events defaultVelocity yamanote) ∷ []

ycpTrack : List MidiTrack
ycpTrack = track "Piano" instrument channel tempo (music→events defaultVelocity ycp) ∷ []
