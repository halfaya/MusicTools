{-# OPTIONS --cubical --safe #-}

module Chord where

open import Interval
open import Pitch

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Data.Fin        using (Fin; toℕ) renaming (zero to fz; suc to fs)
open import Data.List       using (List; map; []; _∷_; _++_; zip)
open import Data.Nat        using (ℕ)
open import Data.Product    using (_×_)
open import Data.String     using (String) renaming (_++_ to _++s_)

open import Function        using (_∘_)

open import AssocList
open import BitVec
open import Pitch
open import Util            using (_+N_)

data Root : Type where
  root : Fin chromaticScaleSize → Root

showRoot : Root → String
showRoot (root fz)                                                        = "I"
showRoot (root (fs fz))                                                   = "♭II"
showRoot (root (fs (fs fz)))                                              = "II"
showRoot (root (fs (fs (fs fz))))                                         = "♭III"
showRoot (root (fs (fs (fs (fs fz)))))                                    = "III"
showRoot (root (fs (fs (fs (fs (fs fz))))))                               = "IV"
showRoot (root (fs (fs (fs (fs (fs (fs fz)))))))                          = "♭V"
showRoot (root (fs (fs (fs (fs (fs (fs (fs fz))))))))                     = "V"
showRoot (root (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))                = "♭VI"
showRoot (root (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))           = "VI"
showRoot (root (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))      = "♭VII"
showRoot (root (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))) = "VII"

data Quality : Type where
  Maj  : Quality
  Min  : Quality
  Dom7 : Quality
  Maj7 : Quality

showQuality : Quality → String
showQuality Maj  = "maj"
showQuality Min  = "min"
showQuality Dom7 = "⁷"
showQuality Maj7 = "maj⁷"

RootQuality : Type
RootQuality = Root × Quality

showRootQuality : RootQuality → String
showRootQuality (r , q) = showRoot r ++s showQuality q

Notes : Type
Notes = BitVec chromaticScaleSize

ChordList : Type
ChordList = AList Notes RootQuality

-- The list should not include the root.
makeChord : Root → List ℕ → Notes
makeChord (root n) []       = BitVec.insert n empty
makeChord (root n) (x ∷ xs) = BitVec.insert (n +N x) (makeChord (root n) xs)

-- The list should not include the root.
qualityNotes : Quality → List ℕ
qualityNotes Maj  = 4 ∷ 7 ∷ []
qualityNotes Min  = 3 ∷ 7 ∷ []
qualityNotes Dom7 = 4 ∷ 7 ∷ 10 ∷ []
qualityNotes Maj7 = 4 ∷ 7 ∷ 11 ∷ []

makeChordQuality : RootQuality → Notes
makeChordQuality (r , q) = makeChord r (qualityNotes q)


---------

--addMajor

aa = show (makeChordQuality (root fz , Maj))

{-
allPairs : {A : Type} → List A → List (A × A)
allPairs []       = []
allPairs (x ∷ xs) = map (x ,_) xs ++ allPairs xs

aa = allPairs (c 5 ∷ e 5 ∷ g 5 ∷ [])
bb = zip aa (map (toℕ ∘ unIntervalClass ∘ pitchPairToIntervalClass) aa)
-}
