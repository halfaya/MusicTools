module Harmony where

open import Data.Bool       using (Bool; true; false)
open import Data.Fin        using (#_)
open import Data.List       using (List; map; []; _∷_; concatMap; foldr)
open import Data.Nat        using (ℕ; suc)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Vec        using (toList)

open import Music
open import Note
open import Pitch

-- either 0 or 1 pitch class
pointToPitchClass : Point → List PitchClass
pointToPitchClass (tone p) = pitchToClass p ∷ []
pointToPitchClass (hold p) = pitchToClass p ∷ []
pointToPitchClass rest     = []

chordToPitchClasses : {n : ℕ} → Chord n → List PitchClass
chordToPitchClasses (chord ps) = concatMap pointToPitchClass (toList ps) 

pitchClassListToSet : List PitchClass → PitchClassSet
pitchClassListToSet = foldr addToPitchClassSet emptyPitchClassSet

pitchClassSetToList : PitchClassSet → List PitchClass
pitchClassSetToList ps = fn 0 (toList ps)
  where fn : ℕ → List Bool → List PitchClass
        fn i []           = []
        fn i (false ∷ bs) = fn (suc i) bs
        fn i (true  ∷ bs) = pitchClass (i mod chromaticScaleSize) ∷ fn (suc i) bs

-- Primary chords, assuming the tonic is pitch class 0.

I-maj I-min IV-maj V-maj : PitchClassSet

I-maj  = pitchClassListToSet (map pitchClass (# 0 ∷ # 4 ∷ # 7  ∷ []))
I-min  = pitchClassListToSet (map pitchClass (# 0 ∷ # 3 ∷ # 7  ∷ []))
IV-maj = pitchClassListToSet (map pitchClass (# 0 ∷ # 5 ∷ # 9  ∷ []))
V-maj  = pitchClassListToSet (map pitchClass (# 2 ∷ # 7 ∷ # 11 ∷ []))

-- Triads, without quality
data Triad : Set where
  I   : Triad
  II  : Triad
  III : Triad
  IV  : Triad
  V   : Triad
  VI  : Triad
  VII : Triad

-- from Table of Usual Root Progressions (Major Mode), Harmony (Piston 5e), page 23
record NextTriad : Set where
  constructor nextTriad
  field
    usual     : List Triad
    sometimes : List Triad
    rare      : List Triad

rootProgression : Triad → NextTriad
rootProgression I   = nextTriad (IV ∷ V   ∷ []) (VI       ∷ []) (II  ∷ III     ∷ [])
rootProgression II  = nextTriad (V        ∷ []) (IV  ∷ VI ∷ []) (I   ∷ III     ∷ [])
rootProgression III = nextTriad (VI       ∷ []) (IV       ∷ []) (I   ∷ II  ∷ V ∷ [])
rootProgression IV  = nextTriad (V        ∷ []) (I   ∷ II ∷ []) (III ∷ VI      ∷ [])
rootProgression V   = nextTriad (I        ∷ []) (IV  ∷ VI ∷ []) (II  ∷ III     ∷ [])
rootProgression VI  = nextTriad (II ∷ V   ∷ []) (III ∷ IV ∷ []) (I             ∷ [])
rootProgression VII = nextTriad (I  ∷ III ∷ []) (VI       ∷ []) (II  ∷ IV  ∷ V ∷ [])
