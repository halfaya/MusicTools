{-# OPTIONS --cubical --safe #-}

module Harmony where

open import Data.Bool       using (Bool; true; false; if_then_else_; _∨_; not; _∧_)
open import Data.Fin        using (#_; toℕ) renaming (zero to fz; suc to fs)
open import Data.List       using (List; map; []; _∷_; concatMap; foldr; head; zip; null)
open import Data.Maybe      using (fromMaybe; is-nothing; Maybe; just; nothing)
open import Data.Nat        using (ℕ; suc; _∸_; _<ᵇ_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec        using (Vec; toList; []; _∷_)
open import Function        using (_∘_)

open import BitVec          using (BitVec; empty; insert; elements; _∩_; _∈_)
open import Counterpoint
open import Diatonic        using (DiatonicDegree; thirdUp; _≡ᵈ_; degree→PC; major; pitch→DegreeCMajor)
open import Interval
open import Music
open import Note
open import Pitch           hiding (I)
open import Util            using (filter; concatMaybe)

-- either 0 or 1 pitch class
pointToPC : Point → List PC
pointToPC (tone p) = pitchToClass p ∷ []
pointToPC (hold p) = pitchToClass p ∷ []
pointToPC rest     = []

chordToPCes : {n : ℕ} → Chord n → List PC
chordToPCes (chord ps) = concatMap pointToPC (toList ps) 

pitchClassListToSet : List PC → PCSet
pitchClassListToSet = foldr insert empty

pitchClassSetToList : PCSet → List PC
pitchClassSetToList ps = fn 0 (toList ps)
  where fn : ℕ → List Bool → List PC
        fn i []           = []
        fn i (false ∷ bs) = fn (suc i) bs
        fn i (true  ∷ bs) = i mod s12 ∷ fn (suc i) bs

-- Primary chords, assuming the tonic is pitch class 0.

I-maj I-min IV-maj V-maj : PCSet

I-maj  = pitchClassListToSet (# 0 ∷ # 4 ∷ # 7  ∷ [])
I-min  = pitchClassListToSet (# 0 ∷ # 3 ∷ # 7  ∷ [])
IV-maj = pitchClassListToSet (# 0 ∷ # 5 ∷ # 9  ∷ [])
V-maj  = pitchClassListToSet (# 2 ∷ # 7 ∷ # 11 ∷ [])

-- Triads, without quality
data Triad : Set where
  I   : Triad
  II  : Triad
  III : Triad
  IV  : Triad
  V   : Triad
  VI  : Triad
  VII : Triad

--data Triad : Set where
--  I : Triad; II : Triad; III : Triad; IV : Triad; V : Triad; VI : Triad; VII : Triad

allTriads : List Triad
allTriads = I ∷ II ∷ III ∷ IV ∷ V ∷ VI ∷ VII ∷ []

triadRoot : Triad → DiatonicDegree
triadRoot I   = (# 0)
triadRoot II  = (# 1)
triadRoot III = (# 2)
triadRoot IV  = (# 3)
triadRoot V   = (# 4)
triadRoot VI  = (# 5)
triadRoot VII = (# 6)

rootTriad : DiatonicDegree → Triad
rootTriad fz                                 = I
rootTriad ((fs fz))                          = II
rootTriad ((fs (fs fz)))                     = III
rootTriad ((fs (fs (fs fz))))                = IV
rootTriad ((fs (fs (fs (fs fz)))))           = V
rootTriad ((fs (fs (fs (fs (fs fz))))))      = VI
rootTriad ((fs (fs (fs (fs (fs (fs fz))))))) = VII

triadDegrees : Triad → Vec DiatonicDegree 3
triadDegrees t =
  let root = triadRoot t
      third = thirdUp root
      fifth = thirdUp third
  in root ∷ third ∷ fifth ∷ []

infix 4 _≡ᵗ_
_≡ᵗ_ : Triad → Triad → Bool
t ≡ᵗ u = triadRoot t ≡ᵈ triadRoot u

TriadSet : Set
TriadSet = BitVec s7

triadListToSet : List Triad → TriadSet
triadListToSet []       = empty
triadListToSet (t ∷ ts) = insert (triadRoot t) (triadListToSet ts)

triadSetToList : TriadSet → List Triad
triadSetToList ts = map rootTriad (elements ts)

containingTriads : DiatonicDegree → List Triad
containingTriads fz                                 = I   ∷ IV  ∷ VI  ∷ []
containingTriads ((fs fz))                          = II  ∷ V   ∷ VII ∷ []
containingTriads ((fs (fs fz)))                     = III ∷ VI  ∷ I   ∷ []
containingTriads ((fs (fs (fs fz))))                = IV  ∷ VII ∷ II  ∷ []
containingTriads ((fs (fs (fs (fs fz)))))           = V   ∷ I   ∷ III ∷ []
containingTriads ((fs (fs (fs (fs (fs fz))))))      = VI  ∷ II  ∷ IV  ∷ []
containingTriads ((fs (fs (fs (fs (fs (fs fz))))))) = VII ∷ III ∷ V   ∷ []

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
previousTriads I   = V ∷ IV ∷ VII ∷ []
previousTriads II  = VI ∷ IV ∷ []
previousTriads III = VI ∷ VII ∷ []
previousTriads IV  = I ∷ V ∷ II ∷ III ∷ []
previousTriads V   = I ∷ IV ∷ II ∷ VI ∷ []
previousTriads VI  = IV ∷ I ∷ II ∷ V ∷ VII ∷ []
previousTriads VII = []

harmonizations : {n : ℕ} → Vec DiatonicDegree n → List (Vec Triad n)
harmonizations [] = []
harmonizations (d ∷ []) = map (_∷ []) (containingTriads d)
harmonizations (d ∷ d' ∷ ds) =
  let tss = harmonizations (d' ∷ ds)
      dTriads  = containingTriads d
  in concatMap (λ t → concatMaybe (map (prependTriad t) tss)) dTriads
  where
    prevOk : Triad → Triad → Bool
    prevOk t x = (triadRoot t) ∈ triadListToSet (previousTriads x)
    prependTriad : {n : ℕ} → Triad → Vec Triad (suc n) → Maybe (Vec Triad (suc (suc n)))
    prependTriad t ts = if prevOk t (Data.Vec.head ts) then just (t ∷ ts) else nothing

halfCadence : {n : ℕ} → Vec Triad n → Bool
halfCadence []           = false
halfCadence (t ∷ [])     = t ≡ᵗ V
halfCadence (_ ∷ t ∷ ts) = halfCadence (t ∷ ts)

-- Given a pitch p and a diatontic degree d, return a pitch that
-- has degree d and is 1-2 octaves lower than p.
pitchLower : Pitch → DiatonicDegree → Pitch
pitchLower p d =
  let (c , o) = absoluteToRelative p
      c'      = degree→PC major d
  in relativeToAbsolute (c' , o ∸ 2)

-- Given a soporano voice s a pitch and the other voices
-- as diatonic degrees of a major scale, voice the
-- accompaniment in close position.
voiceChord : Pitch → Vec DiatonicDegree 3 → Vec Pitch 3
voiceChord s (a ∷ t ∷ b ∷ [])  =
  let (s' , o) = absoluteToRelative s
      a'       = degree→PC major a
      t'       = degree→PC major t
      b'       = degree→PC major b
      ao       = downOctave a' s' o
      to       = downOctave t' a' ao
      bo       = downOctave b' t' to
  in relativeToAbsolute (a' , ao) ∷
     relativeToAbsolute (t' , to) ∷
     relativeToAbsolute (b' , bo) ∷ []
  where downOctave : PC → PC → Octave → Octave
        downOctave pc₁ pc₂ o =
          if toℕ pc₁ <ᵇ toℕ pc₂ then o
          else (o ∸ 1)

-- Given a soprano pitch p and a triad harmonization t,
-- generate a list of possible bass notes.
-- Assumes p is in t. Only the root of the triad is
-- allowed to be doubled.
-- Each bass note is pitched 1-2 octaves below p.
bassNotes : Pitch → Triad → List Pitch
bassNotes p t =
  let sop  = pitch→DegreeCMajor p
      root = triadRoot t
      ds   = toList (triadDegrees t)
      ds'  = filter (λ d → (sop ≡ᵈ root) ∨ not (sop ≡ᵈ d)) ds
  in map (pitchLower p) ds'

-- Given a soprano pitch p and a triad harmonization t,
-- generate a harmonizing chord in root position.
-- Assumes p is in t. Only the root of the triad is
-- allowed to be doubled.
-- Each bass note is pitched 1-2 octaves below p.
-- Alto and Tenor fit inside.
-- Currently root or third is preferred for alto.
harmonizingChord : Pitch → Triad → Vec Pitch 3
harmonizingChord p t =
  let sop   = pitch→DegreeCMajor p
      root  = triadRoot t
      third = thirdUp root
      fifth = thirdUp third
      alto  = if sop ≡ᵈ root then third else root
      tenor = if sop ≡ᵈ fifth then third else fifth
  in voiceChord p (alto ∷ tenor ∷ root ∷ [])
  where
    remove : DiatonicDegree → Vec DiatonicDegree 3 → Vec DiatonicDegree 2
    remove sop (d ∷ d₁ ∷ d₂ ∷ []) =
      if d ≡ᵈ sop then d₁ ∷ d₂ ∷ []
      else (if d₁ ≡ᵈ sop then d ∷ d₂ ∷ [] else d ∷ d₁ ∷ [])

-- Create 4 part harmonizations ending in V for a melody in C major.
voicedHarmonizations : {n : ℕ} → Vec Pitch n → List (Vec (Vec Pitch 4) n)
voicedHarmonizations {n} ps =
  let ds = Data.Vec.map pitch→DegreeCMajor ps
      hs : List (Vec Triad n)
      hs = filter halfCadence (harmonizations ds)
  in map (λ ts → Data.Vec.map (λ pt → proj₁ pt ∷ harmonizingChord (proj₁ pt) (proj₂ pt))
                              (Data.Vec.zip ps ts)) hs

-- Check interval between each pair of voices.
intervalsOkFilter : Vec Pitch 4 → Bool
intervalsOkFilter (s ∷ a ∷ t ∷ b ∷ []) =
  null (concatMaybe (map (intervalCheck ∘ toPitchInterval)
--                         ((s , a) ∷ (s , t) ∷ (s , b) ∷ (a , t) ∷ (a , b) ∷ (t , b) ∷ [])))
                         ((s , a) ∷ (s , b) ∷ (s , t) ∷ [])))

filterIntervalsOk : {n : ℕ} → List (Vec (Vec Pitch 4) n) → List (Vec (Vec Pitch 4) n)
filterIntervalsOk xs =
  let f : List (Vec Pitch 4) → Bool
      f xs = foldr _∧_ true (map intervalsOkFilter xs)
  in filter (f ∘ toList) xs

motionErrors : {n : ℕ} → Vec (Vec Pitch 4) n → List MotionError
motionErrors xs =
  let ss = Data.Vec.map (Data.Vec.head) xs
      as = Data.Vec.map (Data.Vec.head ∘ Data.Vec.tail) xs
      ts = Data.Vec.map (Data.Vec.head ∘ Data.Vec.tail ∘ Data.Vec.tail) xs
      bs = Data.Vec.map (Data.Vec.head ∘ Data.Vec.tail ∘ Data.Vec.tail ∘ Data.Vec.tail) xs

      sas = map toPitchInterval (toList (Data.Vec.zip as ss))
      sts = map toPitchInterval (toList (Data.Vec.zip ts ss))
      sbs = map toPitchInterval (toList (Data.Vec.zip bs ss))
      ats = map toPitchInterval (toList (Data.Vec.zip ts as))
      abs = map toPitchInterval (toList (Data.Vec.zip bs as))
      tbs = map toPitchInterval (toList (Data.Vec.zip bs ts))
  in concatMap checkMotion (sas ∷ sts ∷ sbs ∷ ats ∷ abs ∷ tbs ∷ [])

--filterSBMotionOk : {n : ℕ} → List (Vec (Vec Pitch 4) n) → List (Vec (Vec Pitch 4) n)
--filterSBMotionOk = filter motionOkFilter

-- Given a soprano line with harmonization, generate
-- a list of possible bass lines 1-1 with soprano notes.
-- The SB counterpoint must satisfy 1st species
-- interval and motion rules.
bassLines : List (Pitch × Triad) → List (List Pitch)
-- We need to make the base case a singleton list of an empty list for
-- the general case to work. Possibly look into modifying the general
-- case to handle a base case of an empty list.
bassLines [] = [] ∷ []
bassLines ((sop , triad) ∷ pts) =
  let pss = bassLines pts
      basses  = bassNotes sop triad
      intervalOkSBs : List PitchInterval -- list of bass notes with interval (to sop) that pass intervalCheck
      intervalOkSBs = filter (is-nothing ∘ intervalCheck) (map (toPitchInterval ∘ (_, sop)) basses)
      intervalOkBs = map proj₁ intervalOkSBs
      intervalOkBassLines = concatMap (λ ps → (map (_∷ ps) intervalOkBs)) pss
  in filter (mCheck sop (Data.Maybe.map proj₁ (head pts))) intervalOkBassLines
  where
    -- Given a soprano pitch, possibly a second soprano pitch and a list of
    -- bass pitches, if the second soprano pitch exists and there are at
    -- least two bass pitches, check that the motion from the first SB pair to
    -- the second is allowed. If there aren't two SB pairs, return true.
    mCheck : Pitch → Maybe Pitch → List Pitch → Bool
    mCheck _ nothing  _               = true
    mCheck _ (just _) []              = true
    mCheck _ (just _) (_ ∷ [])        = true
    mCheck s₁ (just s₂) (b₁ ∷ b₂ ∷ _) =
      let sb₁ = toPitchInterval (b₁ , s₁)
          sb₂ = toPitchInterval (b₂ , s₂)
      in (is-nothing ∘ uncurry motionCheck) (sb₁ , sb₂)

-- Given a soprano line with harmonization, generate
-- a list of possible triads 1-1 with soprano notes.
-- All pairwise counterpoint must satisfy 1st species
-- interval and motion rules.
chordProg : List (Pitch × Triad) → List (List Pitch)
-- We need to make the base case a singleton list of an empty list for
-- the general case to work. Possibly look into modifying the general
-- case to handle a base case of an empty list.
chordProg [] = [] ∷ []
chordProg ((sop , triad) ∷ pts) =
  let pss = chordProg pts
      basses  = bassNotes sop triad
      intervalOkSBs : List PitchInterval -- list of bass notes with interval (to sop) that pass intervalCheck
      intervalOkSBs = filter (is-nothing ∘ intervalCheck) (map (toPitchInterval ∘ (_, sop)) basses)
      intervalOkBs = map proj₁ intervalOkSBs
      intervalOkBassLines = concatMap (λ ps → (map (_∷ ps) intervalOkBs)) pss
  in filter (mCheck sop (Data.Maybe.map proj₁ (head pts))) intervalOkBassLines
  where
    -- Given a soprano pitch, possibly a second soprano pitch and a list of
    -- bass pitches, if the second soprano pitch exists and there are at
    -- least two bass pitches, check that the motion from the first SB pair to
    -- the second is allowed. If there aren't two SB pairs, return true.
    mCheck : Pitch → Maybe Pitch → List Pitch → Bool
    mCheck _ nothing  _               = true
    mCheck _ (just _) []              = true
    mCheck _ (just _) (_ ∷ [])        = true
    mCheck s₁ (just s₂) (b₁ ∷ b₂ ∷ _) =
      let sb₁ = toPitchInterval (b₁ , s₁)
          sb₂ = toPitchInterval (b₂ , s₂)
      in (is-nothing ∘ uncurry motionCheck) (sb₁ , sb₂)
