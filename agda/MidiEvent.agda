module MidiEvent where

open import Data.Fin     using (Fin; #_)
open import Data.List    using (List; _∷_; []; _++_)
open import Data.Integer using (ℤ; +_; _-_)
open import Data.Nat     using (ℕ; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁)

open import Music        using (Music; _∷_; _∥_; note)
open import Note         using (note; rest; duration)
open import Pitch        using (Pitch; transpose)

-- General MIDI instrument numbers range from 1 to 128,
-- so this is the actual instrument number minus 1.
InstrumentNumber-1 : Set
InstrumentNumber-1 = Fin 128

Tick : Set
Tick = ℕ

Velocity : Set
Velocity  = Fin 128

defaultVelocity : Fin 128
defaultVelocity = # 60

-- percussion is channel 10, so 9 here
Channel-1 : Set
Channel-1 = Fin 16

-- in bpm
Tempo : Set
Tempo = ℕ

-- Midi note value of middle C (C3 by Yamaha standard)
middleC : ℤ
middleC = + 60

record MidiEvent : Set where
  constructor midiEvent
  field
    pitch            : Pitch
    start            : Tick
    stop             : Tick
    velocity         : Velocity

record MidiTrack : Set where
  constructor track
  field
    instrumentNumber : InstrumentNumber-1
    channel          : Channel-1
    tempo            : Tempo -- initial tempo
    events           : List MidiEvent

music→events : Velocity → Music → List MidiEvent
music→events v m = proj₁ (me 0 m) where
  me : Tick → Music → List MidiEvent × Tick
  me t (note (note (duration d) p)) = midiEvent (transpose middleC p) t (t + d) v ∷ [] , t + d
  me t (note (rest (duration d)))   = [] , t + d
  me t (m₁ ∷ m₂)                    = let mes₁ , t₁ = me t  m₁
                                          mes₂ , t₂ = me t₁ m₂
                                      in mes₁ ++ mes₂ , t₂
  me t (m₁ ∥ m₂)                    = let mes₁ , t₁ = me t m₁
                                          mes₂ , t₂ = me t m₂
                                      in mes₁ ++ mes₂ , t₁ ⊔ t₂
