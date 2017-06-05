{-# LANGUAGE UnicodeSyntax #-}

module Midi where

import Note
import Event
import Codec.Midi

defaultVelocity ∷ Velocity
defaultVelocity = 60

-- Midi note value of middle C
middleC ∷ Int
middleC = 60

addMessage ∷ Channel → TimedEvent → Track Ticks → Track Ticks
addMessage c (Notes ns@(n:ns'), d) ts = map (\n -> (0, NoteOn  c n defaultVelocity)) ns ++
                                        [(d, NoteOff  c n defaultVelocity)] ++
                                        map (\n -> (0, NoteOff c n defaultVelocity)) ns' ++ ts
addMessage c (Notes [], d) ts         = ts                                        
addMessage c (Silence, d)  ((t,m):ts) = (t+d,m):ts
addMessage c (Silence, d)  []         = []

-- ticks is the number of ticks per beat (by default a beat is a quarter note)
toMidi ∷ Channel → Int → [TimedEvent] → Midi
toMidi c ticks es = let track = foldr (addMessage c) [(0, TrackEnd)] es
                    in Midi SingleTrack (TicksPerBeat ticks) [track]
