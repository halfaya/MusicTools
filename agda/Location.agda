{-# OPTIONS --erased-cubical --safe #-}

module Location where

open import Prelude

open import Util using (_divℕ_; _modℕ_)

Voice Bar Beat : Type
Voice = ℕ
Bar   = ℕ
Beat  = ℕ

data Location : Type where
  voiceBeat    : Voice →       Beat → Location
  voiceBarBeat : Voice → Bar → Beat → Location

-- Assumes bars and beats are indexed starting at 1
toVoiceBeat : ℕ → Location → Location
toVoiceBeat _           vb@(voiceBeat _ _)        = vb
toVoiceBeat beatsPerBar (voiceBarBeat v bar beat) = voiceBeat v (pred bar * beatsPerBar + beat)

-- Assumes bars and beats are indexed starting at 1
-- For now assume no pickup bar.
toVoiceBarBeat : (n : ℕ) → Location → Location
toVoiceBarBeat beatsPerBar     (voiceBeat    v b )  =
  voiceBarBeat v (suc ((pred b) divℕ beatsPerBar)) (suc ((pred b) modℕ beatsPerBar))
toVoiceBarBeat _           vbb@(voiceBarBeat _ _ _) = vbb

showLocation : Location → String
showLocation (voiceBeat    v     b)    = "Voice " ++s primShowNat v ++s " Beat " ++s primShowNat b
showLocation (voiceBarBeat v bar beat) =
  "Voice " ++s primShowNat v ++s " Bar " ++s primShowNat bar ++s " Beat " ++s primShowNat beat

data Located (A : Type) : Type where
  located : Location → A → Located A

showLocated : {A : Type} → (A → String) → Located A → String
showLocated show (located loc x) = showLocation loc ++s ": " ++s show x

-- Assumes first voice is the lower one, and assigns 1 to higher voice and 2 to lower voice.
index2VoiceBeat : {A : Type} → List (A × A) → List (Located A × Located A)
index2VoiceBeat xs = i2vb 1 xs where -- start counting at beat 1
  i2vb : {A : Type} → ℕ → List (A × A) → List (Located A × Located A)
  i2vb n []             = []
  i2vb n ((a , b) ∷ xs) = (located (voiceBeat 2 n) a , located (voiceBeat 1 n) b) ∷ i2vb (suc n) xs

data Range : Type where
  location : Location → Range
  range    : Location → Location → Range -- start and end of the range, left high voice first

showRange : Range → String
showRange (location loc) = "[" ++s showLocation loc ++s "]"
showRange (range l1 l2)  = "[" ++s showLocation l1 ++s ", " ++s showLocation l2 ++s "]"

toVBrange : ℕ → Range → Range
toVBrange n (location loc) = location (toVoiceBeat n loc)
toVBrange n (range  l1 l2) = range (toVoiceBeat n l1) (toVoiceBeat n l2)

toVBBrange : ℕ → Range → Range
toVBBrange n (location loc) = location (toVoiceBarBeat n loc)
toVBBrange n (range  l1 l2) = range (toVoiceBarBeat n l1) (toVoiceBarBeat n l2)

data Ranged (A : Type) : Type where
  ranged : Range → A → Ranged A

unrange : {A : Type} → Ranged A → A
unrange (ranged _ x) = x

-- Creates a range from (Voice 1, Beat 1) to (Voice 2, Beat n) where n is the length of the list.
fullRange2 : {A : Type} → List A → Range
fullRange2 xs = range (voiceBeat 1 1) (voiceBeat 2 (length xs))

mapRange : {A : Type} → (Range → Range) → Ranged A → Ranged A
mapRange f (ranged r x) = ranged (f r) x

mapRanged : {A B : Type} → (A → B) → Ranged A → Ranged B
mapRanged f (ranged r x) = ranged r (f x)

showRanged : {A : Type} → (A → String) → Ranged A → String
showRanged show (ranged r x) = showRange r ++s " " ++s show x
