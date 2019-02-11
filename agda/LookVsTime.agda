{-# OPTIONS --without-K #-}

module LookVsTime where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_])
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take)
open import Data.Nat     using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_; uncurry)
open import Function     using (_∘_)

open import Pitch
open import Note
open import Music        hiding (map)
open import Midi
open import MidiEvent
open import Util

tempo : ℕ
tempo = 84

----

melodyChannel : Channel-1
melodyChannel = # 0

melodyInstrument : InstrumentNumber-1
melodyInstrument = # 8 -- celesta

melodyNotes : List Note
melodyNotes =
  note (8th 3) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 3) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 1) (e 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 1) (e 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 1) (a 5) ∷
  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 2) (e 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 1) (a 5) ∷
  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 2) (e 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 3) (b 4) ∷
  note (8th 5) (c 5) ∷

  note (8th 1) (f 5) ∷
  note (8th 1) (e 5) ∷
  note (8th 1) (d 5) ∷
  note (8th 5) (c 5) ∷

  note (8th 3) (g 5) ∷
  note (8th 3) (e 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 3) (g 5) ∷
  note (8th 3) (e 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 8) (c 5) ∷

  note (8th 8) (b 4) ∷

  note (8th 3) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 3) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 3) (a 5) ∷
  note (8th 5) (f 5) ∷

  note (8th 3) (e 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 8) (c 5) ∷

  note (8th 8) (d 5) ∷

  note (8th 1) (c 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 1) (c 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 5) (d 5) ∷

  note (8th 3) (a 5) ∷
  note (8th 5) (f 5) ∷

  note (8th 3) (a 5) ∷
  note (8th 5) (g 5) ∷

  note (8th 1) (a 5) ∷
  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 2) (e 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 1) (a 5) ∷
  note (8th 1) (g 5) ∷
  note (8th 1) (f 5) ∷
  note (8th 2) (e 5) ∷
  note (8th 1) (c 5) ∷
  note (8th 2) (d 5) ∷

  note (8th 3) (b 4) ∷
  note (8th 5) (c 5) ∷

  note (8th 24) (b 4) ∷

  []

melodyTrack : MidiTrack
melodyTrack = track "Melody" melodyInstrument melodyChannel tempo (music→events defaultVelocity (fromNotes melodyNotes))

----

accompChannel : Channel-1
accompChannel = # 1

accompInstrument : InstrumentNumber-1
accompInstrument = # 11 -- vibraphone

accompRhythm : List Duration
accompRhythm = map 8th (3 ∷ 3 ∷ 2 ∷ [])

accompF accompFA accompB2 accompC4 : List Pitch
accompF  = f 4 ∷ a 4 ∷ c 5 ∷ []
accompFA = f 4 ∷ a 4 ∷ []
accompB2 = f 4 ∷ b 4 ∷ d 4 ∷ []
accompC4 = f 4 ∷ c 5 ∷ e 5 ∷ []

accompChords1 accompChords2 accompChords3 accompChords4 accompChords5 accompChords : List Chord
accompChords6 accompChords7 : List Chord

accompChords1 = map (uncurry chord)
                    (zip (repeat 8 accompRhythm)
                         (repeat 2 (concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ accompB2 ∷ [])))))
                         
accompChords2 = chord (whole 4) accompFA ∷ []

accompChords3 = map (uncurry chord)
                    (zip (repeat 4 accompRhythm)
                         ((concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ [])))
                          ++        (accompB2 ∷ accompB2 ∷ accompF ∷ [])))

accompChords4 = map (uncurry chord) (zip accompRhythm (replicate 3 accompFA))

accompChords5 = chord (8th (8 + 8 + 6)) accompF ∷ chord (8th 2) accompF ∷ []

accompChords6 = chord (8th (8 + 6))    accompB2 ∷ chord (8th 2) accompB2 ∷ []

accompChords7 = chord (whole 2) accompF ∷ []

accompChords  = accompChords1 ++ accompChords3 ++ accompChords2 ++ accompChords3 ++ accompChords4
                ++ accompChords5 ++ accompChords6 ++ accompChords7
  
accompTrack : MidiTrack
accompTrack = track "Accomp" accompInstrument accompChannel tempo (music→events defaultVelocity (fromChords accompChords))

----

bassChannel : Channel-1
bassChannel = # 2

bassInstrument : InstrumentNumber-1
bassInstrument = # 33 -- finger bass

bassMelody : List Pitch
bassMelody = c 3 ∷ e 3 ∷ f 3 ∷ g 3 ∷ []

bassRhythm : List Duration
bassRhythm = map 8th (3 ∷ 1 ∷ 2 ∷ 2 ∷ [])

bassNotes : List Note
bassNotes = repeat 28 (map (uncurry note) (zip bassRhythm bassMelody))

bassTrack : MidiTrack
bassTrack = track "Bass" bassInstrument bassChannel tempo (music→events defaultVelocity (fromNotes bassNotes))

----

drumInstrument : InstrumentNumber-1
drumInstrument = # 0 -- SoCal?

drumChannel : Channel-1
drumChannel = # 9

drumRhythmA : List Duration
drumRhythmA = map 16th (2 ∷ [])

drumRhythmB : List Duration
drumRhythmB = map 16th (1 ∷ 1 ∷ 2 ∷ [])

drumRhythm : List Duration
drumRhythm = drumRhythmA ++ repeat 3 drumRhythmB ++ drumRhythmA

drumPitches : List Pitch
drumPitches = replicate (length drumRhythm) (b 4) -- Ride In

drumNotes : List Note
drumNotes = rest (whole 1) ∷ repeat 27 (map (uncurry note) (zip drumRhythm drumPitches))

drumTrack : MidiTrack
drumTrack = track "Drums" drumInstrument drumChannel tempo (music→events defaultVelocity (fromNotes drumNotes))

----

lookVsTime : List MidiTrack
lookVsTime = melodyTrack ∷ accompTrack ∷ bassTrack ∷ drumTrack ∷ []
