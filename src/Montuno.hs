{-# LANGUAGE UnicodeSyntax #-}

module Montuno where

import Note
import Chord
import Event

c, eg, f, ac, g, bd ∷ Chord

-- C3 is the base note
c = map (* 12) [0, 1, 2]
f = transpose 5 c
g = transpose 7 c

eg = [4, 7, 4 + 12, 7 + 12]
ac = transpose 5 eg
bd = transpose 7 eg

ex8 ∷ [TimedEvent]
ex8 = [(Notes c,  2),
       (Notes eg, 1),
       (Notes f,  2),
       (Notes ac, 2),
       (Notes g,  2),
       (Notes bd, 2),
       (Notes f,  2),
       (Notes ac, 2),
       (Notes c,  1)]
       
