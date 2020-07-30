{-# OPTIONS --without-K --safe #-}

module FarmFugue where

open import Data.List       using (List; _∷_; []; map; _++_)
open import Data.Nat        using (ℕ)
open import Data.Sign       renaming (+ to s+ ; - to s-)

open import Canon           using (makeCanon; makeTracks)
open import Interval
open import Note
open import Pitch
open import MidiEvent
open import Util            using (repeat)
open import Transformation

--------------

b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : List Note

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
  tone half (g 4) ∷
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
  tone half (f 5) ∷
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

subject countersubject extra line1 : List Note
subject = b1 ++ b3 ++ b1 ++ b4
countersubject = map (transposeNoteInterval (makeSigned s- per5)) (b5 ++ b6 ++ b5 ++ b7)
extra = b8 ++ b10 ++ b9 ++ b10
line1 = subject ++ countersubject ++ extra

transpositions : List SignedInterval
transpositions = map (makeSigned s-) (per1 ∷ per5 ∷ per8 ∷ [])

fugue : List (List Note)
fugue = makeCanon line1 2 (whole d+ whole d+ whole d+ whole) transpositions

tempo : ℕ
tempo = 160

fugueTracks : List MidiTrack
fugueTracks = makeTracks tempo fugue
