{-# LANGUAGE UnicodeSyntax #-}

module Midi where

import Scale
import Event
import Codec.Midi

defaultVelocity ∷ Velocity
defaultVelocity = 60

defaultTicksPerBeat ∷ Int
defaultTicksPerBeat = 4

addMessage ∷ Channel → TimedEvent → Track Ticks → Track Ticks
addMessage c (Note n, d) ts       = [(0, NoteOn c n defaultVelocity), (d, NoteOff c n defaultVelocity)] ++ ts
addMessage c (Silence, d) ((t,m):ts) = (t+d,m):ts
addMessage c (Silence, d) []         = []

toMidi ∷ Channel → [TimedEvent] → Midi
toMidi c es = let track = foldr (addMessage c) [(0, TrackEnd)] es
              in Midi SingleTrack (TicksPerBeat defaultTicksPerBeat) [track]
