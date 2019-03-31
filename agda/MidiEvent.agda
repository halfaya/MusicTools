{-# OPTIONS --without-K #-}

module MidiEvent where

open import Data.Fin     using (Fin; #_)
open import Data.List    using (List; _∷_; []; _++_)
open import Data.Nat     using (ℕ; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String  using (String)

open import Music        using (Music; _∷_; _∥_; note)
open import Note         using (note; rest; duration)
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

-- percussion is channel 10, so 9 as Channel-1
Channel-1 : Set
Channel-1 = Fin 16

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

music→events : Velocity → Music → List MidiEvent
music→events v m = proj₁ (me 0 m) where
  me : Tick → Music → List MidiEvent × Tick
  me t (note (note (duration d) p)) = midiEvent p t (t + d) v ∷ [] , t + d
  me t (note (rest (duration d)))   = [] , t + d
  me t (m₁ ∷ m₂)                    = let mes₁ , t₁ = me t  m₁
                                          mes₂ , t₂ = me t₁ m₂
                                      in mes₁ ++ mes₂ , t₂
  me t (m₁ ∥ m₂)                    = let mes₁ , t₁ = me t m₁
                                          mes₂ , t₂ = me t m₂
                                      in mes₁ ++ mes₂ , t₁ ⊔ t₂
