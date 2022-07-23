{-# OPTIONS --cubical --safe #-}

module Chord where

open import Prelude

open import AssocList
open import BitVec
open import Pitch
open import Util            using (_+N_; _∘_)

data Root : Type where
  root : Fin s12 → Root

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
  maj  : Quality
  min  : Quality
  dom7 : Quality
  maj7 : Quality

showQuality : Quality → String
showQuality maj  = "maj"
showQuality min  = "min"
showQuality dom7 = "⁷"
showQuality maj7 = "maj⁷"

RootQuality : Type
RootQuality = Root × Quality

showRootQuality : RootQuality → String
showRootQuality (r , q) = showRoot r ++s showQuality q

Notes : Type
Notes = BitVec s12

ChordList : Type
ChordList = AList Notes RootQuality

-- The list should not include the root.
makeChord : Root → List ℕ → Notes
makeChord (root n) []       = BitVec.insert n empty
makeChord (root n) (x ∷ xs) = BitVec.insert (n +N x) (makeChord (root n) xs)

-- The list should not include the root.
qualityNotes : Quality → List ℕ
qualityNotes maj  = 4 ∷ 7 ∷ []
qualityNotes min  = 3 ∷ 7 ∷ []
qualityNotes dom7 = 4 ∷ 7 ∷ 10 ∷ []
qualityNotes maj7 = 4 ∷ 7 ∷ 11 ∷ []

makeChordQuality : RootQuality → Notes
makeChordQuality (r , q) = makeChord r (qualityNotes q)


---------

--addMajor

aa = show (makeChordQuality (root fz , maj))

{-
allPairs : {A : Type} → List A → List (A × A)
allPairs []       = []
allPairs (x ∷ xs) = map (x ,_) xs ++ allPairs xs

aa = allPairs (c 5 ∷ e 5 ∷ g 5 ∷ [])
bb = zip aa (map (toℕ ∘ unIntervalClass ∘ pitchPairToIntervalClass) aa)
-}
