{-# OPTIONS --without-K #-}

module Piston where

open import Data.Bool using (Bool; true; not; _∨_)
open import Data.Fin
open import Data.List using (List; map; _∷_; []; concatMap; zip; drop)
open import Data.Maybe using (fromMaybe; is-nothing)
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Function using (_∘_)
--open import Data.Vec using (Vec; []; _∷_; zip; toList) renaming (map to vmap)

open import Relation.Binary.PropositionalEquality using (refl)

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

-- test

mDegrees = concatMap fff melody117s
  where fff : Note → List DiatonicDegree
        fff (tone _ p) = pitchToDegreeCMajor p ∷ []
        fff (rest _)   = []
aaa = map triadSetToList (harmonizations mDegrees)
{-
(I ∷ V ∷ []) ∷
(I ∷ []) ∷
(I ∷ []) ∷
(II ∷ IV ∷ []) ∷
(I ∷ IV ∷ VI ∷ []) ∷
(III ∷ V ∷ []) ∷
(II ∷ IV ∷ VI ∷ []) ∷
(I ∷ III ∷ V ∷ []) ∷ []
-}

------

-- Code to generate B given S

-- Given a pitch p and a diatontic degree d, return a pitch that
-- has degree d and is 1-2 octaves lower than p.
pitchLower : Pitch → DiatonicDegree → Pitch
pitchLower p d =
  let (c , o) = absoluteToRelative p
      c'      = degreeToPitchClassMajor d
  in relativeToAbsolute (c' , octave (unoctave o ∸ 2))

-- assume pitch is in triad
bassNotes : Pitch → Triad → List Pitch
bassNotes p t =
  let sop  = pitchToDegreeCMajor p
      root = triadRoot t
      ds   = triadDegrees t
      ds'  = filter (λ d → (sop ≡ᵈ root) ∨ not (sop ≡ᵈ d)) ds
  in map (pitchLower p) ds'

bassLines : List (Pitch × Triad) → List (List Pitch)
bassLines [] = []
bassLines ((p , t) ∷ []) =
  let ps = bassNotes p t
      pis = filter (is-nothing ∘ intervalCheck) (map (pitchPairToPitchInterval ∘ (_, p)) ps)
      goodBs = map proj₁ pis
  in map (_∷ []) goodBs
bassLines ((p1 , t1) ∷ pt2@(p2 , t2) ∷ pts) =
  let pss = bassLines (pt2 ∷ pts)
      ps  = bassNotes p1 t1
      pis = filter (is-nothing ∘ intervalCheck) (map (pitchPairToPitchInterval ∘ (_, p1)) ps)
      intervalOkBs = map proj₁ pis
      intervalOkLs = concatMap (λ ps → (map (_∷ ps) intervalOkBs)) pss
  in filter mCheck intervalOkLs
  where
  -- assume argument has at least 2 elements
  mCheck : List Pitch → Bool
  mCheck []             = true -- unreachable
  mCheck (b ∷ [])       = true -- unreachable
  mCheck (b1 ∷ b2 ∷ bs) =
    let pi1 = pitchPairToPitchInterval (b1 , p1)
        pi2 = pitchPairToPitchInterval (b2 , p2)
    in (is-nothing ∘ uncurry motionCheck) (pi1 , pi2)

pitches117s : List Pitch
pitches117s = g 5 ∷ g 5 ∷ e 5 ∷ g 5 ∷ a 5 ∷ c 6 ∷ b 5 ∷ a 5 ∷ g 5 ∷ []

triads117 : List Triad
triads117 = V ∷ V ∷ I ∷ I ∷ IV ∷ VI ∷ III ∷ IV ∷ V ∷ []

pts117 : List (Pitch × Triad)
pts117 = zip pitches117s triads117

bbb = bassLines (drop 5 pts117)
ccc = pitch 43 ∷ pitch 47 ∷ pitch 38 ∷ []
ddd = (map (pitchPairToPitchInterval ∘ (_, g 5)) ccc)
eee = filter (is-nothing ∘ intervalCheck) ddd

-- 36 : c 3
-- 40 : e 3
-- 41 : f 3
-- 43 : g 3
-- 47 : b 3
-- 52 : e 4
-- 57 : a 4
