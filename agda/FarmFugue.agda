{-# OPTIONS --without-K --safe #-}

module FarmFugue where

open import Data.Fin        using (#_)
open import Data.List       using (List; _∷_; []; map; _++_)
open import Data.Nat        using (ℕ; _*_)
open import Data.Sign       using () renaming (+ to s+ ; - to s-)
open import Data.Vec        using (Vec; _∷_; []; lookup) renaming (map to vmap)
open import Function        using (_∘_)

open import Canon           using (makeCanon; makeTrackList)
open import Interval
open import Music
open import Note
open import Pitch
open import MidiEvent
open import Util            using (repeat)
open import Transformation

--------------

b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : List Note
b4' : List Note

b1 =
  tone 8th  (c 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (e 5) ∷
  rest 8th        ∷
  tone 8th  (e 5) ∷
  rest 8th        ∷
  tone 8th  (c 5) ∷
  rest 8th        ∷
  []

b2 =
  tone 8th  (c 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (c 5) ∷
  tone 8th  (d 5) ∷
  tone qtr  (e 5) ∷
  tone qtr  (c 5) ∷
  []

b3 =
  tone dqtr (e 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (e 5) ∷
  []

b4 =
  tone dqtr (e 5) ∷
  tone 8th  (e 5) ∷
  tone qtr  (g 4) ∷
  tone qtr  (b 4) ∷
  []

b4' =
  tone dqtr (e 5) ∷
  tone 8th  (e 5) ∷
  tone qtr  (g 4) ∷
  tone half (b 4) ∷
  []

b5 =
  tone 8th  (c 6) ∷
  rest 8th        ∷
  tone 8th  (a 5) ∷
  rest 8th        ∷
  tone 8th  (e 5) ∷
  tone 8th  (f 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (f 5) ∷
  []

b6 =
  tone 8th  (c 6) ∷
  rest 8th        ∷
  tone 8th  (a 5) ∷
  rest 8th        ∷
  tone half (c 5) ∷
  []

b7 =
  tone 8th  (c 5) ∷
  rest 8th        ∷
  tone 8th  (e 5) ∷
  rest 8th        ∷
  tone 8th  (f 5) ∷
  rest 8th        ∷
  tone 8th  (d 5) ∷
  rest 8th        ∷
  []

b8 =
  tone 8th  (g 5) ∷
  tone 8th  (g 5) ∷
  tone 8th  (f 5) ∷
  tone 8th  (f 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (d 5) ∷
  []

b9 =
  tone qtr  (g 5) ∷
  tone qtr  (f 5) ∷
  tone qtr  (e 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (d 5) ∷
  []

b10 =
  tone dqtr (c 5) ∷
  tone 8th  (c 5) ∷
  tone 8th  (c 5) ∷
  rest 8th        ∷
  tone 8th  (c 5) ∷
  rest 8th        ∷
  []

b11 =
  tone qtr  (b 5) ∷
  tone qtr  (a 5) ∷
  tone qtr  (g 5) ∷
  tone qtr  (f 5) ∷
  []

subject countersubject extra base : List Note

subject = b1 ++ b3 ++ b1 ++ b4
countersubject = map (transposeNoteInterval (makeSigned s- per5)) (b5 ++ b6 ++ b5 ++ b7)
extra = b8 ++ b10 ++ b9 ++ b10
base = subject ++ countersubject ++ extra

transpositions : Vec SignedInterval 3
transpositions = vmap (makeSigned s-) (per1 ∷ per5 ∷ per8 ∷ [])

-- Exposition is a truncated canon
expo exposition : Vec (List Note) 3
expo = makeCanon base 2 (whole d+ whole d+ whole d+ whole) transpositions
-- Truncate to first 20 bars (16 16th notes per bar in 4/4 time)
exposition = vmap (melody→notes ∘ fixLength (20 * 16) ∘ notes→melody) expo

-- Variation
subject' base' : List Note

subject' = b1 ++ b3 ++ b1 ++ b4'
base' = subject' ++ countersubject ++ extra

expo' exposition' : Vec (List Note) 3
expo' = makeCanon base' 2 (whole d+ whole d+ whole d+ whole) transpositions
exposition' = vmap (melody→notes ∘ fixLength (20 * 16) ∘ notes→melody) expo'

-- Some basic development
-- Development is still a work in progress. Right now the piece abruptly ends after the exposition.

dev1 dev2 dev3 line1 line2 line3 : List Note

dev1 =
  map (transposeNoteInterval (makeSigned s+ per8)) b1
  ++ tone whole (e 6) ∷ []

dev2 =
  map (transposeNoteInterval (makeSigned s+ per1)) b1
  ++ tone whole (g 5) ∷ []

dev3 = 
  map (transposeNoteInterval (makeSigned s- per8)) b1
  ++ tone whole (c 4) ∷ []

line1 = lookup exposition (# 0) ++ lookup exposition' (# 0) ++ dev1
line2 = lookup exposition (# 1) ++ lookup exposition' (# 1) ++ dev2
line3 = lookup exposition (# 2) ++ lookup exposition' (# 2) ++ dev3

fugue : Vec (List Note) 3
fugue = line1 ∷ line2 ∷ line3 ∷ []

tempo : ℕ
tempo = 160

fugueTracks : List MidiTrack
fugueTracks = makeTrackList tempo fugue
