module Midi where

open import Data.Integer
open import Data.List
open import Data.Product

open import Note
open import Chord
open import TimedChord

{-# FOREIGN GHC import qualified Codec.Midi as M #-}

-- types from Codec.Midi
Channel  = ℤ -- 0 - 15
Ticks    = ℤ -- 0 - (2^28 - 1)
Velocity = ℤ -- 0 - 127

postulate
  Track : Set → Set

--type Track a = [(a,Message)]
{-# COMPILE GHC Track = type Track #-}

defaultVelocity : Velocity
defaultVelocity = + 60

-- Midi note value of middle C
middleC : ℤ
middleC = + 60

-- TODO: Convert Codec.Mido to Agda
addMessage : Channel → TimedChord → Track Ticks → Track Ticks
addMessage c (chord [] , d) ts = {!!}
addMessage c (chord (x ∷ x₁) , d) ts = {!!}
--addMessage c (chord (ns@(ote n:ns')), Duration d) ts
--  = map (\(Note n) -> (0, NoteOn  c n defaultVelocity)) ns ++
--    [(d, NoteOff  c n defaultVelocity)] ++
--    map (\(Note n) -> (0, NoteOff c n defaultVelocity)) ns' ++ ts
--addMessage c (Chord [], Duration d)                ((t,m):ts) = (t+d,m):ts
--addMessage c (Chord [], _)                         []         = []

{-
-- ticks is the number of ticks per beat (by default a beat is a quarter note)
toMidi ∷ Channel → Int → [TimedChord] → Midi
toMidi c ticks es = let track = foldr (addMessage c) [(0, TrackEnd)] es
                    in Midi SingleTrack (TicksPerBeat ticks) [track]
-}
