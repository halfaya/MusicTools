{-# OPTIONS --erased-cubical --safe #-}

module Location where

open import Prelude

open import Util using (_divℕ_; _modℕ_; zipWithIndex)

Voice Bar Beat BeatsPerBar : Type
Voice = ℕ
Bar   = ℕ
Beat  = ℕ
BeatsPerBar = ℕ

-- Convention is that voice and beat are indexed starting at 1.
data Location : Type where
  location : Voice → Beat → Location

data VoiceBarBeat : Type where
  voiceBarBeat : BeatsPerBar → Voice → Bar → Beat → VoiceBarBeat

toLocation : VoiceBarBeat → Location
toLocation (voiceBarBeat beatsPerBar v bar beat) = location v (pred bar * beatsPerBar + beat)

-- For now assume no pickup bar.
toVoiceBarBeat : BeatsPerBar → Location → VoiceBarBeat
toVoiceBarBeat beatsPerBar (location v b) =
  voiceBarBeat beatsPerBar v (suc ((pred b) divℕ beatsPerBar)) (suc ((pred b) modℕ beatsPerBar))

infix 4 _==loc_ _≤loc_

_==loc_ : Location → Location → Bool
location a b ==loc location c d = (a == c) ∧ (b == d)

_≤loc_ : Location → Location → Bool
location a b ≤loc location c d = (a ≤ᵇ c) ∧ (b ≤ᵇ d)

showLocation : Location → String
showLocation (location v b)    = "Voice " ++s primShowNat v ++s " Beat " ++s primShowNat b

showVoiceBarBeat : VoiceBarBeat → String
showVoiceBarBeat (voiceBarBeat _ v bar beat) =
  "Voice " ++s primShowNat v ++s " Bar " ++s primShowNat bar ++s " Beat " ++s primShowNat beat

showVBB : BeatsPerBar → Location → String
showVBB b = showVoiceBarBeat ∘ toVoiceBarBeat b

data Located (A : Type) : Type where
  located : Location → A → Located A

unlocate : {A : Type} → Located A → A
unlocate (located _ x) = x

showLocated : {A : Type} → (A → String) → Located A → String
showLocated show (located loc x) = showLocation loc ++s ": " ++s show x

mapLocated : {A B : Type} → (A → B) → Located A → Located B
mapLocated f (located l x) = located l (f x)

-- Assumes first voice is the lower one, and assigns 1 to higher voice and 2 to lower voice.
index2VoiceBeat : {A : Type} → List (A × A) → List (Located A × Located A)
index2VoiceBeat xs = i2vb 1 xs where -- start counting at beat 1
  i2vb : {A : Type} → ℕ → List (A × A) → List (Located A × Located A)
  i2vb n []             = []
  i2vb n ((a , b) ∷ xs) = (located (location 2 n) a , located (location 1 n) b) ∷ i2vb (suc n) xs

index1VoiceBeat : {A : Type} → ℕ → List A → List (Located A)
index1VoiceBeat voice xs =
  let f x = located (location voice (suc (fst x))) (snd x)
  in map f (zipWithIndex xs)

indexVoiceBeat : {A : Type} → List (List A) → List (List (Located A))
indexVoiceBeat xs = 
  let f x = index1VoiceBeat (suc (fst x)) (snd x)
  in map f (zipWithIndex xs)

data Range : Type where
  point     : Location → Range
  rectangle : Location → Location → Range -- left high and right low points of rectangle

showRange : Range → String
showRange (point loc)        = "[" ++s showLocation loc ++s "]"
showRange (rectangle l1 l2)  = "[" ++s showLocation l1 ++s ", " ++s showLocation l2 ++s "]"

showVBBRange : BeatsPerBar → Range → String
showVBBRange b (point loc)        = "[" ++s showVBB b loc ++s "]"
showVBBRange b (rectangle l1 l2)  = "[" ++s showVBB b l1 ++s ", " ++s showVBB b l2 ++s "]"

_∈range_ : Location → Range → Bool
x ∈range point y        = x ==loc y
x ∈range rectangle a b  = (a ≤loc x) ∧ (x ≤loc b) 

data Ranged (A : Type) : Type where
  ranged : Range → A → Ranged A

unrange : {A : Type} → Ranged A → A
unrange (ranged _ x) = x

-- Creates a range from (Voice 1, Beat 1) to (Voice 2, Beat n) where n is the length of the list.
fullRange2 : {A : Type} → List A → Range
fullRange2 xs = rectangle (location 1 1) (location 2 (length xs))

mapRange : {A : Type} → (Range → Range) → Ranged A → Ranged A
mapRange f (ranged r x) = ranged (f r) x

mapRanged : {A B : Type} → (A → B) → Ranged A → Ranged B
mapRanged f (ranged r x) = ranged r (f x)

showRanged : {A : Type} → (A → String) → Ranged A → String
showRanged show (ranged r x) = showRange r ++s " " ++s show x

showVBBRanged : {A : Type} → BeatsPerBar → (A → String) → Ranged A → String
showVBBRanged b show (ranged r x) = showVBBRange b r ++s " " ++s show x
