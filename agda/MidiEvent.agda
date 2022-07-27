{-# OPTIONS --erased-cubical --safe #-}

module MidiEvent where

open import Data.Fin     using (Fin; #_)
open import Data.List    using (List; _∷_; []; concat; map)
open import Data.Nat     using (ℕ; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String  using (String)
open import Data.Vec     using (toList)
open import Function     using (_∘_)

open import Music        using (Melody; melody; Counterpoint; cp; Harmony; melody→notes; harmony→counterpoint)
open import Note         using (Note; tone; rest)
open import Pitch        using (Pitch)

-- General MIDI instrument numbers range from 1 to 128,
-- so this is the actual instrument number minus 1.
InstrumentNumber-1 : Set
InstrumentNumber-1 = Fin 128

Tick : Set
Tick = ℕ

Velocity : Set
Velocity  = Fin 128

defaultVelocity : Velocity
defaultVelocity = # 60

maxChannels : ℕ
maxChannels = 16

-- percussion is channel 10, so 9 as Channel-1
Channel-1 : Set
Channel-1 = Fin maxChannels

-- a few pre-defined channels
channel1 channel2 channel3 channel4 : Channel-1
channel1 = # 0
channel2 = # 1
channel3 = # 2
channel4 = # 3

-- in bpm
Tempo : Set
Tempo = ℕ

record MidiEvent : Set where
  constructor midiEvent
  field
    pitch            : Pitch -- Pitch was defined to correspond to MIDI pitch
    start            : Tick
    stop             : Tick
    velocity         : Velocity

record MidiTrack : Set where
  constructor track
  field
    trackName        : String
    instrumentNumber : InstrumentNumber-1
    channel          : Channel-1
    tempo            : Tempo -- initial tempo
    events           : List MidiEvent

notes→events : Velocity → List Note → List MidiEvent
notes→events v ns = me 0 ns where
  me : Tick → List Note → List MidiEvent
  me t [] = []
  me t (tone d p ∷ ns) = midiEvent p t (t + d) v ∷ me (t + d) ns
  me t (rest d   ∷ ns) = me (t + d) ns

melody→events : {n : ℕ} → Velocity → Melody n → List MidiEvent
melody→events v = notes→events v ∘ melody→notes

counterpoint→events : {v d : ℕ} → Velocity → Counterpoint v d → List MidiEvent
counterpoint→events v (cp ms) = concat (map (melody→events v) (toList ms))

harmony→events : {v d : ℕ} → Velocity → Harmony v d → List MidiEvent
harmony→events v = counterpoint→events v ∘ harmony→counterpoint
