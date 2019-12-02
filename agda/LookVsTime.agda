{-# OPTIONS --without-K #-}

module LookVsTime where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_])
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take)
open import Data.Nat     using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_; uncurry)
open import Data.Vec     using (fromList)
open import Function     using (_∘_)

open import Pitch
open import Note         using (tone; rest; Note; Duration; duration; unduration)
open import Music
open import Midi
open import MidiEvent
open import Util         using (repeat)

tempo : ℕ
tempo = 84

----

8th : ℕ → Duration
8th n = duration (2 * n)

whole : ℕ → Duration
whole n = duration (16 * n)

makeHarmony : (d : Duration) → (ps : List Pitch) → Harmony (length ps) (unduration d)
makeHarmony d = pitches→harmony d ∘ fromList

melodyChannel : Channel-1
melodyChannel = # 0

melodyInstrument : InstrumentNumber-1
melodyInstrument = # 8 -- celesta

melodyNotes : List Note
melodyNotes =
  tone (8th 3) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 3) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 1) (e 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 1) (e 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 1) (a 5) ∷
  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 2) (e 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 1) (a 5) ∷
  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 2) (e 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 3) (b 4) ∷
  tone (8th 5) (c 5) ∷

  tone (8th 1) (f 5) ∷
  tone (8th 1) (e 5) ∷
  tone (8th 1) (d 5) ∷
  tone (8th 5) (c 5) ∷

  tone (8th 3) (g 5) ∷
  tone (8th 3) (e 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 3) (g 5) ∷
  tone (8th 3) (e 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 8) (c 5) ∷

  tone (8th 8) (b 4) ∷

  tone (8th 3) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 3) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 3) (a 5) ∷
  tone (8th 5) (f 5) ∷

  tone (8th 3) (e 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 8) (c 5) ∷

  tone (8th 8) (d 5) ∷

  tone (8th 1) (c 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 1) (c 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 5) (d 5) ∷

  tone (8th 3) (a 5) ∷
  tone (8th 5) (f 5) ∷

  tone (8th 3) (a 5) ∷
  tone (8th 5) (g 5) ∷

  tone (8th 1) (a 5) ∷
  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 2) (e 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 1) (a 5) ∷
  tone (8th 1) (g 5) ∷
  tone (8th 1) (f 5) ∷
  tone (8th 2) (e 5) ∷
  tone (8th 1) (c 5) ∷
  tone (8th 2) (d 5) ∷

  tone (8th 3) (b 4) ∷
  tone (8th 5) (c 5) ∷

  tone (8th 24) (b 4) ∷

  []

melodyTrack : MidiTrack
melodyTrack = track "Melody" melodyInstrument melodyChannel tempo (notes→events defaultVelocity melodyNotes)

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

--accompChords1 accompChords2 accompChords3 accompChords4 accompChords5 accompChords6 accompChords7 : List (List Note)

{-
accompChords1 = map (uncurry makeHarmony)
                    (zip (repeat 8 accompRhythm)
                         (repeat 2 (concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ accompB2 ∷ [])))))
-}

accompChords2 = makeHarmony (whole 4) accompFA ∷ []

{-
accompChords3 = map (uncurry makeHarmony)
                    (zip (repeat 4 accompRhythm)
                         ((concat (map (replicate 3) (accompF ∷ accompB2 ∷ accompC4 ∷ [])))
                          ++        (accompB2 ∷ accompB2 ∷ accompF ∷ [])))
-}

--accompChords4 = map (uncurry makeHarmony) (zip accompRhythm (replicate 3 accompFA))

accompChords5 : Harmony 3 48
accompChords5 = makeHarmony (8th (8 + 8 + 6)) accompF +H+ makeHarmony (8th 2) accompF

accompChords6 : Harmony 3 32
accompChords6 = makeHarmony (8th (8 + 6)) accompB2 +H+ makeHarmony (8th 2) accompB2

accompChords7 : Harmony 3 32
accompChords7 = makeHarmony (whole 2) accompF

{-
accompChords : List (List Note)
accompChords = accompChords1 ++ accompChords3 ++ accompChords2 ++ accompChords3 ++ accompChords4
                 ++ accompChords5 ++ accompChords6 ++ accompChords7
-}

accompTrack : MidiTrack
accompTrack = track "Accomp" accompInstrument accompChannel tempo (harmony→events defaultVelocity {!!})

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
bassNotes = repeat 28 (map (uncurry tone) (zip bassRhythm bassMelody))

bassTrack : MidiTrack
bassTrack = track "Bass" bassInstrument bassChannel tempo (notes→events defaultVelocity bassNotes)

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
drumPitches = replicate (length drumRhythm) (b 4) -- Ride In

drumNotes : List Note
drumNotes = rest (whole 1) ∷ repeat 27 (map (uncurry tone) (zip drumRhythm drumPitches))

drumTrack : MidiTrack
drumTrack = track "Drums" drumInstrument drumChannel tempo (notes→events defaultVelocity drumNotes)

----

lookVsTime : List MidiTrack
lookVsTime = melodyTrack ∷ accompTrack ∷ bassTrack ∷ drumTrack ∷ []
