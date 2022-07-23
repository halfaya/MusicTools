{-# OPTIONS --erased-cubical --safe #-}

module Prelude where

open import Cubical.Core.Everything     public using (_≡_; Level; Type; _≃_; ~_)

open import Cubical.Foundations.Prelude public using (refl; sym; _∙_; cong; transport; subst; funExt; transp)

open import Data.Bool       public using (Bool; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Integer    public using (ℤ; +_; -[1+_]; _-_; ∣_∣; -_)
open import Data.Fin        public using (Fin; #_; toℕ; inject; fromℕ; fromℕ<; inject₁) renaming (zero to fz; suc to fs)
open import Data.List       public using (List; []; _∷_; _∷ʳ_; foldl; foldr; map; reverse; length; _++_; take; drop; concat; zip; replicate; sum)
open import Data.Maybe      public using (Maybe; just; nothing)
open import Data.Nat        public using (ℕ; zero; suc; pred; _+_; _*_; _<ᵇ_; _≤ᵇ_; _<?_; _≟_; _∸_; s≤s; z≤n; _⊓_; _⊔_; ⌊_/2⌋) renaming (_≡ᵇ_ to _==_)
open import Data.Nat.DivMod public using (_mod_; _div_)
open import Data.Integer.DivMod public using (_modℕ_)
open import Data.Sign       public using (Sign)
open import Data.Sum        public using (_⊎_; inj₁; inj₂)
open import Data.String     public using (String; intersperse) renaming (_++_ to _++s_)
open import Data.Product    public using (_×_; _,_; Σ; proj₁; proj₂; uncurry)
open import Data.Vec        public using (Vec; []; _∷_; lookup; _[_]%=_; toList; updateAt; head; last; foldr₁; zipWith) renaming (concat to cat; replicate to rep; map to vmap; _∷ʳ_ to _v∷ʳ_; zip to vzip; reverse to vreverse; _++_ to _++v_; take to vtake; drop to vdrop)
