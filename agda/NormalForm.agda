{-# OPTIONS --cubical --safe #-}

module NormalForm where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Data.Bool       using (Bool; false; true; if_then_else_)
open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.List       using (List; []; _∷_; foldr; length; map)
open import Data.Maybe      using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat        using (ℕ; zero; suc; pred; _+_; _*_; _∸_; _≡ᵇ_; _>_; _<ᵇ_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Vec        using (Vec; []; _∷_; lookup; replicate; _[_]%=_; toList) renaming (map to vmap)

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert; empty; show)
open import Util
open import Pitch
open import Interval

_≤[]_ : List ℕ → List ℕ → Bool
[]       ≤[] ys = true
(x ∷ xs) ≤[] [] = false
(x ∷ xs) ≤[] (y ∷ ys) =
  if x ≡ᵇ y
  then xs ≤[] ys
  else (if x <ᵇ y then true else false)

_≤[opci]_ : List PitchClass → List PitchClass → Bool
_≤[opci]_ xs ys =
  (map (toℕ ∘ unOrderedIntervalClass) (pcIntervals xs)) ≤[]
  (map (toℕ ∘ unOrderedIntervalClass) (pcIntervals ys))

bestPitchClassList : List PitchClass → List (List PitchClass) → List PitchClass
bestPitchClassList xs         []         = xs
bestPitchClassList []         (ys ∷ yss) = bestPitchClassList ys yss
bestPitchClassList xs@(_ ∷ _) (ys ∷ yss) =
  if xs ≤[opci] ys
  then bestPitchClassList xs yss
  else bestPitchClassList ys yss

normalForm : PitchClassSet → List PitchClass
normalForm pcs =
  let xs  = fromPitchClassSet pcs
  in bestPitchClassList [] (iter rotateLeft (pred (length xs)) xs)

bestNormalForm : PitchClassSet → List PitchClass
bestNormalForm pcs =
  let xs = normalForm pcs
      ys = normalForm (I pcs)
  in if xs ≤[opci] ys then xs else ys

primeForm : PitchClassSet → List PitchClass
primeForm pcs with bestNormalForm pcs
... | []                    = []
... | xs@(pitchClass p ∷ _) = map (Tp (toℕ (opposite p))) xs

-- Test

--ss = vmap pitchClass (# 4 ∷ # 7 ∷ # 9 ∷ [])
ss = vmap pitchClass (# 2 ∷ # 0 ∷ # 5 ∷ # 6 ∷ [])
--ss = vmap pitchClass (# 8 ∷ # 9 ∷ # 11 ∷ # 0 ∷ # 4 ∷ [])
--ss = vmap pitchClass (# 8 ∷ # 7 ∷ # 4 ∷ # 3 ∷ # 11 ∷ # 0 ∷ [])

aa = show (toPitchClassSet (toList ss))
bb = fromPitchClassSet (toPitchClassSet (toList ss))
cc = map (toℕ ∘ unPitchClass) (normalForm (toPitchClassSet (toList ss)))
dd = map (toℕ ∘ unPitchClass) (bestNormalForm (toPitchClassSet (toList ss)))
ee = map (toℕ ∘ unPitchClass) (primeForm (toPitchClassSet (toList ss)))
ff = icVector (primeForm (toPitchClassSet (toList ss)))
gg = map (toℕ ∘ unPitchClass) (fromPitchClassSet (T 8 (toPitchClassSet (toList ss))))

