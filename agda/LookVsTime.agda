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

repeat : ∀ {a} {A : Set a} → (n : ℕ) → List A → List A
repeat n = concat ∘ replicate n

----

tempo : ℕ
tempo = 84

----

-- duration in 8th notes
8th : ℕ → Duration
8th n = duration (2 * n)

----

melodyChannel : Channel-1
melodyChannel = # 0

melodyInstrument : InstrumentNumber-1
melodyInstrument = # 0 -- piano

melodyNotes : List Note
melodyNotes =
  note (8th 3) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 3) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 1) (e 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 1) (e 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 1) (a 3) ∷
  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 2) (e 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 1) (a 3) ∷
  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 2) (e 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 3) (b 2) ∷
  note (8th 5) (c 3) ∷

  note (8th 1) (f 3) ∷
  note (8th 1) (e 3) ∷
  note (8th 1) (d 3) ∷
  note (8th 5) (c 3) ∷

  note (8th 3) (g 3) ∷
  note (8th 3) (e 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 3) (g 3) ∷
  note (8th 3) (e 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 8) (c 3) ∷

  note (8th 8) (b 2) ∷

  note (8th 3) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 3) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 3) (a 3) ∷
  note (8th 5) (f 3) ∷

  note (8th 3) (e 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 8) (c 3) ∷

  note (8th 8) (d 3) ∷

  note (8th 1) (c 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 1) (c 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 5) (d 3) ∷

  note (8th 3) (a 3) ∷
  note (8th 5) (f 3) ∷

  note (8th 3) (a 3) ∷
  note (8th 5) (g 3) ∷

  note (8th 1) (a 3) ∷
  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 2) (e 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 1) (a 3) ∷
  note (8th 1) (g 3) ∷
  note (8th 1) (f 3) ∷
  note (8th 2) (e 3) ∷
  note (8th 1) (c 3) ∷
  note (8th 2) (d 3) ∷

  note (8th 3) (b 2) ∷
  note (8th 5) (c 3) ∷

  note (8th 24) (b 2) ∷

  []

melodyTrack : MidiTrack
melodyTrack = track melodyInstrument melodyChannel tempo (music→events defaultVelocity (fromNotes melodyNotes))

----

accompChannel : Channel-1
accompChannel = # 1

accompInstrument : InstrumentNumber-1
accompInstrument = # 11 -- vibraphone

accompRhythm : List Duration
accompRhythm = map (duration ∘ (_* 2)) (3 ∷ 3 ∷ 2 ∷ [])

accompF accompFA accompB2 accompC4 : List Pitch
accompF  = map pitch (-[1+ 6 ] ∷ -[1+ 2 ] ∷ + 0 ∷ [])
accompFA = take 2 accompF
accompB2 = map pitch (-[1+ 6 ] ∷ -[1+ 0 ] ∷ + 2 ∷ [])
accompC4 = map pitch (-[1+ 6 ] ∷ + 0 ∷ + 4 ∷ [])

accompChords1 accompChords2 accompChords3 accompChords4 accompChords5 accompChords : List Chord
accompChords6 accompChords7 : List Chord

accompChords1 = map (uncurry chord)
                    (zip (repeat 8 accompRhythm)
                         (repeat 2 (concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ accompB2 ∷ [])))))
                         
accompChords2 = chord (duration (16 * 4)) accompFA ∷ []

accompChords3 = map (uncurry chord)
                    (zip (repeat 4 accompRhythm)
                         ((concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ [])))
                          ++        (accompB2 ∷ accompB2 ∷ accompF ∷ [])))

accompChords4 = map (uncurry chord) (zip accompRhythm (replicate 3 accompFA))

accompChords5 = chord (duration (2 * (8 + 8 + 6))) accompF ∷ chord (duration (2 * 2)) accompF ∷ []

accompChords6 = chord (duration (2 * (8 + 6))) accompB2 ∷ chord (duration (2 * 2)) accompB2 ∷ []

accompChords7 = chord (duration (2 * (8 + 8))) accompF ∷ []

accompChords  = accompChords1 ++ accompChords3 ++ accompChords2 ++ accompChords3 ++ accompChords4
                ++ accompChords5 ++ accompChords6 ++ accompChords7
  
accompTrack : MidiTrack
accompTrack = track accompInstrument accompChannel tempo (music→events defaultVelocity (fromChords accompChords))

----

bassChannel : Channel-1
bassChannel = # 2

bassInstrument : InstrumentNumber-1
bassInstrument = # 33 -- finger bass

bassMelodyRel : List RelativePitch
bassMelodyRel = map (scaleDegreeToRelativePitch majorScale ∘ scaleDegree)
                 (# 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ [])

bassMelody : List Pitch
bassMelody = map (relativeToAbsolute ∘ (_, octave -[1+ 1 ])) bassMelodyRel

bassRhythm : List Duration
bassRhythm = map (duration ∘ (_* 2)) (3 ∷ 1 ∷ 2 ∷ 2 ∷ [])

bassNotes : List Note
bassNotes = repeat 28 (map (uncurry note) (zip bassRhythm bassMelody))

bassTrack : MidiTrack
bassTrack = track bassInstrument bassChannel tempo (music→events defaultVelocity (fromNotes bassNotes))

----

drumInstrument : InstrumentNumber-1
drumInstrument = # 0 -- SoCal?

drumChannel : Channel-1
drumChannel = # 9

drumRhythmA : List Duration
drumRhythmA = map duration (2 ∷ [])

drumRhythmB : List Duration
drumRhythmB = map duration (1 ∷ 1 ∷ 2 ∷ [])

drumRhythm : List Duration
drumRhythm = drumRhythmA ++ repeat 3 drumRhythmB ++ drumRhythmA

drumPitches : List Pitch
drumPitches = replicate (length drumRhythm) (pitch -[1+ 0 ]) -- Ride In

drumNotes : List Note
drumNotes = rest (duration (16)) ∷ repeat 27 (map (uncurry note) (zip drumRhythm drumPitches))

drumTrack : MidiTrack
drumTrack = track drumInstrument drumChannel tempo (music→events defaultVelocity (fromNotes drumNotes))

----

lookVsTime : List MidiTrack
lookVsTime = melodyTrack ∷ accompTrack ∷ bassTrack ∷ drumTrack ∷ []
