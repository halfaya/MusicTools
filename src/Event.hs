{-# LANGUAGE UnicodeSyntax, GADTs #-}

module Event where

import Scale

data Event where
  Note    ∷ AbsoluteNote → Event
  Silence ∷ Event

-- duration in some unspecified unit
type Duration = Int

type TimedEvent = (Event, Duration)

