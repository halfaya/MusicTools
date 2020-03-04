{-# OPTIONS --without-K #-}

module Piston where

open import Data.Fin     using (#_)
open import Data.List    using (List; map; _∷_; []; concatMap; zip; drop; length; replicate; intercalate)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec     using (Vec; fromList; _∷_; [])
open import Function     using (_∘_)

open import Counterpoint
open import Harmony
open import Note
open import Music
open import MidiEvent
open import Pitch
open import Interval
open import Util

-- 3/4 time
melodyAs : List Note
melodyAs =
  tone dhalf (c 6) ∷
  tone qtr (d 6) ∷ tone qtr (c 6) ∷ tone qtr (e 6) ∷
  tone half (f 6) ∷ tone qtr (f 6) ∷
  tone qtr (g 6) ∷ tone qtr (f 6) ∷ tone qtr (d 6) ∷
  tone half (c 6) ∷ tone qtr (a 5) ∷
  tone qtr (b♭ 5) ∷ tone half (g 5) ∷
  tone dhalf (f 5) ∷ []

-- 4/4 time
melodyBs : List Note
melodyBs =
  tone half (c 6) ∷ tone qtr (b 5) ∷ tone qtr (c 6) ∷
  tone half (d 6) ∷ tone qtr (e 6) ∷ tone qtr (c 6) ∷
  tone half (f 6) ∷ tone half (d 6) ∷
  tone half (b 5) ∷ tone qtr (c 6) ∷ tone qtr (d 6) ∷
  tone half (b 5) ∷ tone half (b 5) ∷
  tone half (c 6) ∷ tone half (c 6) ∷ []


-- 4/4 time
melodyCs : List Note
melodyCs =
  tone qtr (g♯ 5) ∷ tone qtr (g♯ 5) ∷ tone qtr (a 5) ∷ tone qtr (f♯ 5) ∷ 
  tone half (g♯ 5) ∷ tone qtr (g♯ 5) ∷ tone qtr (c♯ 6) ∷
  tone half (b 5) ∷ tone qtr (g♯ 5) ∷ tone qtr (a 5) ∷
  tone half (f♯ 5) ∷ tone half (f♯ 5) ∷
  tone qtr (g♯ 5) ∷ tone qtr (g♯ 5) ∷ tone qtr (a 5) ∷ tone qtr (b 5) ∷ 
  tone half (c♯ 6) ∷ tone half (b 5) ∷
  tone qtr (b 5) ∷ tone qtr (d♯ 5) ∷ tone qtr (e 5) ∷ tone qtr (f♯ 5) ∷ 
  tone whole (e 5) ∷ []

-- This is example 9-1 in the 5th edition of Piston.
-- It was example 117 in a previous edition used in the FHARM paper.
-- 4/4 time
melody117s : List Note
melody117s =
  rest half ∷ tone half (g 5) ∷
  tone half (e 5) ∷ tone half (g 5) ∷
  tone half (a 5) ∷ tone half (c 6) ∷
  tone half (b 5) ∷ tone half (a 5) ∷
  tone whole (g 5) ∷ []

melody117a : List Note
melody117a =
  tone whole (b 4) ∷
  tone half (c 5) ∷ tone half (e 5) ∷
  tone half (f 5) ∷ tone half (e 5) ∷
  tone half (g 5) ∷ tone half (f 5) ∷
  tone whole (d 5) ∷ []

melody117t : List Note
melody117t =
  tone dwhole (g 4) ∷ tone half (c 5) ∷
  tone whole (c 5) ∷
  tone half (e 5) ∷ tone half (c 5) ∷
  tone whole (b 4) ∷ []

melody117b : List Note
melody117b =
  tone whole (g 3) ∷
  tone whole (c 4) ∷
  tone half (f 4) ∷ tone half (a 4) ∷
  tone half (e 4) ∷ tone half (f 4) ∷
  tone whole (g 4) ∷ []

----

piano marimba : InstrumentNumber-1
piano   = # 0
marimba = # 12

channel1 channel2 : Channel-1
channel1 = # 0
channel2 = # 1

tempo : ℕ
tempo = 120

mVelocity cVelocity : Velocity
mVelocity = # 60
cVelocity = # 60

melodyAsTrack : MidiTrack
melodyAsTrack = track "Melody A S" piano channel1 tempo (notes→events mVelocity melodyAs)

melodyATracks : List MidiTrack
melodyATracks =  melodyAsTrack ∷ []

melodyBsTrack : MidiTrack
melodyBsTrack = track "Melody B S" piano channel1 tempo (notes→events mVelocity melodyBs)

melodyBTracks : List MidiTrack
melodyBTracks =  melodyBsTrack ∷ []

melodyCsTrack : MidiTrack
melodyCsTrack = track "Melody C S" piano channel1 tempo (notes→events mVelocity melodyCs)

melodyCTracks : List MidiTrack
melodyCTracks =  melodyCsTrack ∷ []

melody117sTrack : MidiTrack
melody117sTrack = track "Melody 117 S" piano channel1 tempo (notes→events mVelocity melody117s)

melody117aTrack : MidiTrack
melody117aTrack = track "Melody 117 A" piano channel1 tempo (notes→events mVelocity melody117a)

melody117tTrack : MidiTrack
melody117tTrack = track "Melody 117 T" piano channel1 tempo (notes→events mVelocity melody117t)

melody117bTrack : MidiTrack
melody117bTrack = track "Melody 117 B" piano channel1 tempo (notes→events mVelocity melody117b)

melody117Tracks : List MidiTrack
melody117Tracks =  melody117sTrack ∷ melody117aTrack ∷ melody117tTrack ∷ melody117bTrack ∷ []

-----

-- Harmonization of Piston's example 9-1 (117).

pitches117s : List Pitch
pitches117s = g 5 ∷ g 5 ∷ e 5 ∷ g 5 ∷ a 5 ∷ c 6 ∷ b 5 ∷ a 5 ∷ g 5 ∷ []

degrees117 : List DiatonicDegree
degrees117 = map pitchToDegreeCMajor pitches117s

-- All harmonizations which include the melody, follow the
-- table of root progressions, and end with V.
-- 25 possibilities.
harms = filter halfCadence (harmonizations degrees117)

triads117 : List Triad
triads117 = (V ∷ I ∷ VI ∷ V ∷ IV ∷ I ∷ V ∷ VI ∷ V ∷ [])

pts117 : List (Pitch × Triad)
pts117 = zip pitches117s triads117

chords117 : List (Vec Pitch 4)
chords117 = map (λ pt → proj₁ pt ∷ harmonizingChord (proj₁ pt) (proj₂ pt)) pts117

chordsPoints117 : List (Vec Point 4)
chordsPoints117 = map (Data.Vec.map tone) chords117

harm117 : Harmony 4 (length chords117)
harm117 = harmony (fromList (map chord chordsPoints117))

testHTrack : MidiTrack
testHTrack = track "Test Harm" piano channel1 tempo (harmony→events mVelocity harm117)

testHTracks : List MidiTrack
testHTracks = testHTrack ∷ []

-------------------

{-
bbb = bassLines pts117

-- 36 : c 3
-- 40 : e 3
-- 41 : f 3
-- 43 : g 3
-- 47 : b 3
-- 52 : e 4
-- 57 : a 4

testS : List Note
testS = intercalate (rest half ∷ []) (replicate (length bbb) (map (tone half) pitches117s))

testB : List Note
testB = intercalate (rest half ∷ []) (map (map (tone half)) bbb)
--map (tone half) (pitch 47 ∷ pitch 43 ∷  pitch 36 ∷ pitch 36 ∷  pitch 41 ∷ pitch 57 ∷ pitch 43 ∷ pitch 41 ∷ pitch 43 ∷ [])

testSTrack : MidiTrack
testSTrack = track "Test S" piano channel1 tempo (notes→events mVelocity testS)

testBTrack : MidiTrack
testBTrack = track "Test B" piano channel1 tempo (notes→events mVelocity testB)
-}

