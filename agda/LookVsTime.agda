{-# OPTIONS --cubical #-}

module LookVsTime where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_])
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take)
open import Data.Nat     using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_; uncurry)
open import Data.Vec     using (fromList; Vec; _∷_; []) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)
open import Function     using (_∘_)

open import Pitch
open import Note         using (tone; rest; Note; Duration; duration; unduration)
open import Music
open import Midi
open import MidiEvent
open import Util         using (repeat; repeatV)

tempo : ℕ
tempo = 84

----

8th : ℕ → Duration
8th n = duration (2 * n)

whole : ℕ → Duration
whole n = duration (16 * n)

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

accompRhythm : Vec Duration 3
accompRhythm = vmap 8th (3 ∷ 3 ∷ 2 ∷ [])

accompF accompB2 accompC4 : Vec Pitch 3
accompF  = f 4 ∷ a 4 ∷ c 5 ∷ []
accompB2 = f 4 ∷ b 4 ∷ d 4 ∷ []
accompC4 = f 4 ∷ c 5 ∷ e 5 ∷ []

accompFA : Vec Pitch 2
accompFA = f 4 ∷ a 4 ∷ []

accompChords1 : Harmony 3 128
accompChords1 =
  foldIntoHarmony (repeatV 8 accompRhythm)
                  (repeatV 2 (vconcat (vmap (rep {n = 3}) (accompF ∷ accompB2 ∷ accompC4 ∷ accompB2 ∷ []))))

accompChords2 : Harmony 3 64
accompChords2 = addEmptyVoice (pitches→harmony (whole 4) accompFA)

accompChords3 : Harmony 3 64
accompChords3 =
  foldIntoHarmony (repeatV 4 accompRhythm)
                  (vconcat (vmap (rep {n = 3}) (accompF ∷ accompB2 ∷ accompC4 ∷ [])) +v (accompB2 ∷ accompB2 ∷ accompF ∷ []))

accompChords4 : Harmony 3 16
accompChords4 = addEmptyVoice (foldIntoHarmony accompRhythm (rep accompFA))

accompChords5 : Harmony 3 48
accompChords5 = pitches→harmony (8th (8 + 8 + 6)) accompF +H+ pitches→harmony (8th 2) accompF

accompChords6 : Harmony 3 32
accompChords6 = pitches→harmony (8th (8 + 6)) accompB2 +H+ pitches→harmony (8th 2) accompB2

accompChords7 : Harmony 3 32
accompChords7 = pitches→harmony (whole 2) accompF

accompChords : Harmony 3 448
accompChords = accompChords1 +H+ accompChords3 +H+ accompChords2 +H+ accompChords3 +H+ accompChords4
                 +H+ accompChords5 +H+ accompChords6 +H+ accompChords7

accompTrack : MidiTrack
accompTrack = track "Accomp" accompInstrument accompChannel tempo (harmony→events defaultVelocity accompChords)

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
