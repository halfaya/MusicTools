{-# OPTIONS --cubical --safe #-}

module NormalForm where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
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
open import Data.Vec        using (Vec; []; _∷_; lookup; replicate; _[_]%=_; toList)

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
  (map (toℕ ∘ unOrderedIntervalClass) (◯pcIntervals xs)) ≤[]
  (map (toℕ ∘ unOrderedIntervalClass) (◯pcIntervals ys))

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

-- Test

aa = show (toPitchClassSet (toList ryukyuScale))
bb = fromPitchClassSet (toPitchClassSet (toList ryukyuScale))
cc = normalForm (toPitchClassSet (toList ryukyuScale))

--41241
--1241 (1421)
--1412 (2141)
