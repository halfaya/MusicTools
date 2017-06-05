{-# LANGUAGE UnicodeSyntax, GADTSyntax #-}

module Event where

import Note

data Event where
  Notes   ∷ [AbsoluteNote] → Event
  Silence ∷ Event
  deriving Show

-- duration in some unspecified unit
type Duration = Int

type TimedEvent = (Event, Duration)

transposeTimedEvent ∷ Int → TimedEvent → TimedEvent
transposeTimedEvent k (Notes ns, d) = (Notes (transpose k ns), d)
transposeTimedEvent k (Silence,  d) = (Silence,                d)

transposeTimedEvents ∷ Int → [TimedEvent] → [TimedEvent]
transposeTimedEvents k = map (transposeTimedEvent k)

