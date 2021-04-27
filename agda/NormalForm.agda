{-# OPTIONS --cubical --safe #-}

module NormalForm where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Data.Bool       using (Bool; false; true)
open import Data.Integer    using (ℤ; +_; -[1+_])
open import Data.Fin        using (Fin; toℕ; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.List       using (List; []; _∷_; foldr; length)
open import Data.Maybe      using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat        using (ℕ; zero; suc; pred; _+_; _*_; _∸_; _≡ᵇ_; _>_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Vec        using (Vec; []; _∷_; map; lookup; replicate; _[_]%=_; toList)

open import Relation.Nullary using (yes; no)

open import BitVec          using (BitVec; insert; empty; show)
open import Util
open import Pitch

normalForm : PitchClassSet → List PitchClass
normalForm pcs =
  let xs  = fromPitchClassSet pcs
      xss = iter rotateLeft (pred (length xs)) xs
  in {!!}

-- Test

aa = show (toPitchClassSet (toList ryukyuScale))
bb = fromPitchClassSet (toPitchClassSet (toList ryukyuScale))

--41241
--1241 (1421)
--1412 (2141)

{-
pitchClass fz List.∷
pitchClass (fs (fs (fs (fs fz)))) List.∷
pitchClass (fs (fs (fs (fs (fs fz))))) List.∷
pitchClass (fs (fs (fs (fs (fs (fs (fs fz))))))) List.∷
pitchClass
(fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))
List.∷ []
-}
