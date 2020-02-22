{-# OPTIONS --without-K #-}

module Harmony where

open import Data.Bool       using (Bool; true; false; if_then_else_)
open import Data.Fin        using (#_) renaming (zero to fz; suc to fs)
open import Data.List       using (List; map; []; _∷_; concatMap; foldr)
open import Data.Nat        using (ℕ; suc)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Vec        using (Vec; toList)
open import Function        using (_∘_)

open import BitVec          using (BitVec; empty; insert; elements; _∩_)
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
pitchClassListToSet = foldr addToPitchClassSet empty

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

allTriads : List Triad
allTriads = I ∷ II ∷ III ∷ IV ∷ V ∷ VI ∷ VII ∷ []

triadRoot : Triad → DiatonicDegree
triadRoot I   = diatonicDegree (# 0)
triadRoot II  = diatonicDegree (# 1)
triadRoot III = diatonicDegree (# 2)
triadRoot IV  = diatonicDegree (# 3)
triadRoot V   = diatonicDegree (# 4)
triadRoot VI  = diatonicDegree (# 5)
triadRoot VII = diatonicDegree (# 6)

rootTriad : DiatonicDegree → Triad
rootTriad (diatonicDegree fz)                               = I
rootTriad (diatonicDegree (fs fz))                          = II
rootTriad (diatonicDegree (fs (fs fz)))                     = III
rootTriad (diatonicDegree (fs (fs (fs fz))))                = IV
rootTriad (diatonicDegree (fs (fs (fs (fs fz)))))           = V
rootTriad (diatonicDegree (fs (fs (fs (fs (fs fz))))))      = VI
rootTriad (diatonicDegree (fs (fs (fs (fs (fs (fs fz))))))) = VII

triadDegrees : Triad → List DiatonicDegree
triadDegrees t =
  let root = triadRoot t
      third = thirdUp root
      fifth = thirdUp third
  in root ∷ third ∷ fifth ∷ []

infix 4 _≡ᵗ_
_≡ᵗ_ : Triad → Triad → Bool
t ≡ᵗ u = triadRoot t ≡ᵈ triadRoot u

TriadSet : Set
TriadSet = BitVec diatonicScaleSize

triadListToSet : List Triad → TriadSet
triadListToSet []       = empty
triadListToSet (t ∷ ts) = insert (undd (triadRoot t)) (triadListToSet ts)

triadSetToList : TriadSet → List Triad
triadSetToList ts = map (rootTriad ∘ diatonicDegree) (elements ts)

containingTriads : DiatonicDegree → List Triad
containingTriads (diatonicDegree fz)                               = I   ∷ IV  ∷ VI  ∷ []
containingTriads (diatonicDegree (fs fz))                          = II  ∷ V   ∷ VII ∷ []
containingTriads (diatonicDegree (fs (fs fz)))                     = III ∷ VI  ∷ I   ∷ []
containingTriads (diatonicDegree (fs (fs (fs fz))))                = IV  ∷ VII ∷ II  ∷ []
containingTriads (diatonicDegree (fs (fs (fs (fs fz)))))           = V   ∷ I   ∷ III ∷ []
containingTriads (diatonicDegree (fs (fs (fs (fs (fs fz))))))      = VI  ∷ II  ∷ IV  ∷ []
containingTriads (diatonicDegree (fs (fs (fs (fs (fs (fs fz))))))) = VII ∷ III ∷ V   ∷ []

-- from Table of Usual Root Progressions (Major Mode), Harmony (Piston 5e), page 23
record NextTriad : Set where
  constructor nextTriad
  field
    usual     : List Triad
    sometimes : List Triad
    rare      : List Triad
open NextTriad

rootProgression : Triad → NextTriad
rootProgression I   = nextTriad (IV ∷ V   ∷ []) (VI       ∷ []) (II  ∷ III     ∷ [])
rootProgression II  = nextTriad (V        ∷ []) (IV  ∷ VI ∷ []) (I   ∷ III     ∷ [])
rootProgression III = nextTriad (VI       ∷ []) (IV       ∷ []) (I   ∷ II  ∷ V ∷ [])
rootProgression IV  = nextTriad (V        ∷ []) (I   ∷ II ∷ []) (III ∷ VI      ∷ [])
rootProgression V   = nextTriad (I        ∷ []) (IV  ∷ VI ∷ []) (II  ∷ III     ∷ [])
rootProgression VI  = nextTriad (II ∷ V   ∷ []) (III ∷ IV ∷ []) (I             ∷ [])
rootProgression VII = nextTriad (I  ∷ III ∷ []) (VI       ∷ []) (II  ∷ IV  ∷ V ∷ [])

previousTriads : Triad → List Triad
previousTriads I   = V ∷ IV ∷ I ∷ [] -- omit VII since you'll get stuck -- TODO: Remove I
previousTriads II  = VI ∷ IV ∷ []
previousTriads III = VI ∷ []     -- omit VII since you'll get stuck
previousTriads IV  = I ∷ []
previousTriads V   = I ∷ IV ∷ II ∷ VI ∷ []
previousTriads VI  = III ∷ I ∷ II ∷ V ∷ []
previousTriads VII = []

harmonizations : List DiatonicDegree → List TriadSet
harmonizations []       = []
harmonizations (d ∷ []) = triadListToSet (containingTriads d) ∷ []
harmonizations (d ∷ d' ∷ ds) with harmonizations (d' ∷ ds)
... | []       = []
... | ts ∷ tss =
  let us = triadListToSet (concatMap previousTriads (triadSetToList ts))
      vs = triadListToSet (containingTriads d)
  in (us ∩ vs) ∷ ts ∷ tss