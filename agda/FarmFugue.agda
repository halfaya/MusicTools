{-# OPTIONS --erased-cubical --safe #-}

module FarmFugue where

open import Data.Bool       using (Bool; true; false; if_then_else_)
open import Data.Fin        using (#_)
open import Data.List       using (List; _∷_; []; map; _++_)
open import Data.Nat        using (ℕ; _*_; _+_)
open import Data.Sign       using () renaming (+ to s+ ; - to s-)
open import Data.Vec        using (Vec; _∷_; []; lookup; foldl₁) renaming (map to vmap)
open import Function        using (_∘_)

open import Canon           using (makeCanon)
open import Interval        --using (makeSigned; per1; per5; per8; Opi)
open import MakeTracks      using (instruments ; makeTrackList)
open import Music           using (melody→notes; notes→melody; fixLength; dropPoints)
open import Note            using (Note; tone; rest; 8th; qtr; dqtr; half; whole; transposeNoteInterval)
open import Pitch           using (a; b; c; d; e; f; g)
open import MidiEvent       using (MidiTrack)
open import Util            using (repeat)
open import Transformation

--------------

b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : List Note

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

b12 =
  tone qtr (c 4) ∷
  tone qtr (c 4) ∷
  []

b13 =
  tone 8th (c 4) ∷
  tone 8th (c 4) ∷
  tone 8th (c 4) ∷
  tone 8th (c 4) ∷
  []


subject countersubject extra base : List Note

subject = b1 ++ b3 ++ b1 ++ b4
countersubject = map (transposeNoteInterval (makeSigned s- per5)) (b5 ++ b6 ++ b5 ++ b7)
extra = b8 ++ b10 ++ b9 ++ b10
base = subject ++ countersubject ++ extra

transpositions : Vec Opi 3
transpositions = vmap (makeSigned s-) (per1 ∷ per5 ∷ per8 ∷ [])

-- Exposition is a truncated canon
expo exposition : Vec (List Note) 3
expo = makeCanon base 2 (whole + whole + whole + whole) transpositions
-- Truncate to first 20 bars (16 16th notes per bar in 4/4 time)
exposition = vmap (melody→notes ∘ fixLength (20 * 16) ∘ notes→melody) expo

-- Variation

doubleLastDuration : List Note → List Note
doubleLastDuration []                         = []
doubleLastDuration (m ∷ n ∷ ns)               = m ∷ doubleLastDuration (n ∷ ns)
doubleLastDuration (tone d p ∷ []) = tone (2 * d) p ∷ []
doubleLastDuration (rest d   ∷ []) = rest (2 * d) ∷ []

makeVariation : List Note → List Note → List Note → Vec (List Note) 3
makeVariation s c e =
  let base = s ++ c ++ e
      expo = makeCanon base 2 (whole + whole + whole + whole) transpositions
  in vmap (melody→notes ∘ fixLength (20 * 16) ∘ notes→melody) expo

makeVariation' : List Note → List Note → List Note → Vec (List Note) 3
makeVariation' s c e =
  let base = s ++ c ++ e
      expo = makeCanon base 2 (whole + whole + whole + whole) transpositions
  in vmap (melody→notes ∘ dropPoints (2 * 16) ∘ fixLength (16 * 16) ∘ notes→melody) expo

v1 v2 v3 variations : Vec (List Note) 3
v1 = makeVariation (doubleLastDuration subject) countersubject extra
v2 = makeVariation' (doubleLastDuration countersubject) extra subject
v3 = makeVariation' (doubleLastDuration extra) subject countersubject 
variations = v1
--  (lookup v1 (# 0) ++ {- lookup v2 (# 0) ++ -} lookup v3 (# 0)) ∷
--  (lookup v1 (# 1) ++ {- lookup v2 (# 1) ++ -} lookup v3 (# 1)) ∷
--  (lookup v1 (# 2) ++ {- lookup v2 (# 2) ++ -} lookup v3 (# 2)) ∷
--  []

dev1 dev2 dev3 end1 end2 end3 line1 line2 line3 : List Note

dev1 =
  map (transposeNoteInterval (makeSigned s+ per12)) countersubject ++
  map (transposeNoteInterval (makeSigned s+ per12)) subject ++
  map (transposeNoteInterval (makeSigned s+ per12)) b8 ++
  map (transposeNoteInterval (makeSigned s+ per8))  b8 ++
  map (transposeNoteInterval (makeSigned s+ per4))  b8 ++
  map (transposeNoteInterval (makeSigned s- maj2))  b9 ++
  map (transposeNoteInterval (makeSigned s- per4))  subject ++
  map (transposeNoteInterval (makeSigned s- per5))  countersubject ++
  map (transposeNoteInterval (makeSigned s+ min3))  b12 ++
  map (transposeNoteInterval (makeSigned s+ maj3))  b12 ++
  map (transposeNoteInterval (makeSigned s+ min3))  b12 ++
  map (transposeNoteInterval (makeSigned s+ maj3))  b13

dev2 =
  map (transposeNoteInterval (makeSigned s+ per8)) subject ++
  map (transposeNoteInterval (makeSigned s+ per8)) countersubject ++
  map (transposeNoteInterval (makeSigned s+ per8)) b8 ++
  map (transposeNoteInterval (makeSigned s+ per4)) b8 ++
  map (transposeNoteInterval (makeSigned s- maj2)) b8 ++
  map (transposeNoteInterval (makeSigned s- maj6)) b9 ++
  map (transposeNoteInterval (makeSigned s- per8)) countersubject ++
  map (transposeNoteInterval (makeSigned s- per8)) subject ++
  map (transposeNoteInterval (makeSigned s- per4)) (b12 ++ b12 ++ b12 ++ b13)

dev3 =
  map (transposeNoteInterval (makeSigned s+ per5))  countersubject ++
  map (transposeNoteInterval (makeSigned s+ per5))  subject ++
  map (transposeNoteInterval (makeSigned s+ per5))  b8 ++
  map (transposeNoteInterval (makeSigned s+ per1))  b8 ++
  map (transposeNoteInterval (makeSigned s- per5))  b8 ++
  map (transposeNoteInterval (makeSigned s- maj9))  b9 ++
  map (transposeNoteInterval (makeSigned s- per12)) subject ++
  map (transposeNoteInterval (makeSigned s- per12)) countersubject ++
  map (transposeNoteInterval (makeSigned s- maj6))  b12 ++
  map (transposeNoteInterval (makeSigned s- min6))  b12 ++
  map (transposeNoteInterval (makeSigned s- maj6))  b12 ++
  map (transposeNoteInterval (makeSigned s- min6))  b13

end1 =
  map (transposeNoteInterval (makeSigned s+ per8)) b1
  ++ tone whole (e 6) ∷ []

end2 =
  map (transposeNoteInterval (makeSigned s+ per1)) b1
  ++ tone whole (g 5) ∷ []

end3 = 
  map (transposeNoteInterval (makeSigned s- per8)) b1
  ++ tone whole (c 4) ∷ []

line1 = lookup exposition (# 0) ++ dev1 ++ lookup variations (# 0) ++ end1
line2 = lookup exposition (# 1) ++ dev2 ++ lookup variations (# 1) ++ end2
line3 = lookup exposition (# 2) ++ dev3 ++ lookup variations (# 2) ++ end3

fugue : Vec (List Note) 3
fugue = line1 ∷ line2 ∷ line3 ∷ []

tempo : ℕ
tempo = 160

-- note that this was originally all piano
fugueTracks : List MidiTrack
fugueTracks = makeTrackList instruments tempo fugue
