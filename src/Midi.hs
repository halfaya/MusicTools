{-# LANGUAGE UnicodeSyntax #-}

module Midi where

import Note
import Chord
import TimedChord
import Codec.Midi

defaultVelocity ∷ Velocity
defaultVelocity = 60

-- Midi note value of middle C
middleC ∷ Int
middleC = 60

addMessage ∷ Channel → TimedChord → Track Ticks → Track Ticks
addMessage c (Chord (ns@(Note n:ns')), Duration d) ts         = map (\(Note n) -> (0, NoteOn  c n defaultVelocity)) ns ++
                                                                [(d, NoteOff  c n defaultVelocity)] ++
                                                                map (\(Note n) -> (0, NoteOff c n defaultVelocity)) ns' ++ ts
addMessage c (Chord [], Duration d)                ((t,m):ts) = (t+d,m):ts
addMessage c (Chord [], _)                         []         = []

-- ticks is the number of ticks per beat (by default a beat is a quarter note)
toMidi ∷ Channel → Int → [TimedChord] → Midi
toMidi c ticks es = let track = foldr (addMessage c) [(0, TrackEnd)] es
                    in Midi SingleTrack (TicksPerBeat ticks) [track]
