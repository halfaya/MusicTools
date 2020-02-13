{-# OPTIONS --without-K #-}

module Properties where

open import Data.Fin renaming (zero to Fzero; suc to Fsuc) hiding (_+_; _≟_)
open import Data.Nat
open import Data.Nat.DivMod using (_mod_; _div_; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (+-comm)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False)
open ≡-Reasoning

open import Pitch

RelAbs : (n : Pitch) → (relativeToAbsolute ∘ absoluteToRelative) n ≡ n
RelAbs (pitch zero) = refl
RelAbs (pitch (suc n)) =
  begin
    (relativeToAbsolute ∘ absoluteToRelative) (pitch (suc n))
  ≡⟨ refl ⟩
    relativeToAbsolute (pitchClass ((suc n) mod chromaticScaleSize) ,
                        octave ((suc n) div chromaticScaleSize))
  ≡⟨ refl ⟩
    pitch (((suc n) div chromaticScaleSize) * chromaticScaleSize +
           (toℕ ((suc n) mod chromaticScaleSize)))
  ≡⟨ cong pitch
          (+-comm (((suc n) div chromaticScaleSize) * chromaticScaleSize)
                  (toℕ ((suc n) mod chromaticScaleSize))) ⟩
    pitch ((toℕ ((suc n) mod chromaticScaleSize)) +
           (((suc n) div chromaticScaleSize) * chromaticScaleSize))
  ≡⟨ cong pitch (sym {!!}) ⟩
  -- ≡⟨ cong pitch (sym (m≡m%n+[m/n]*n n chromaticScaleSize)) ⟩
    pitch (suc n)
  ∎
   
{-
absRelAbs (pitch (+_     zero))    = refl
absRelAbs (pitch (+_     (suc n))) = let x = absRelAbs (pitch (+ n)) in {!!}
absRelAbs (pitch (-[1+_] zero))    = refl
absRelAbs (pitch (-[1+_] (suc n))) = {!!}
-}

AbsRel : (n : PitchOctave) → (absoluteToRelative ∘ relativeToAbsolute) n ≡ n
AbsRel (pitchClass p , octave o) =
  begin
    (absoluteToRelative ∘ relativeToAbsolute) (pitchClass p , octave o)
  ≡⟨ refl ⟩
    absoluteToRelative (pitch (o * chromaticScaleSize + (toℕ p)))
  ≡⟨ refl ⟩
    (pitchClass ((o * chromaticScaleSize + (toℕ p)) mod chromaticScaleSize) ,
                 octave ((o * chromaticScaleSize + (toℕ p)) div chromaticScaleSize))
  ≡⟨ {!!} ⟩
    (pitchClass p , octave o)
  ∎

{-
relAbsRel (relativePitch zero    , octave (+_     zero))    = refl
relAbsRel (relativePitch zero    , octave (+_     (suc n))) = {!!}
relAbsRel (relativePitch zero    , octave (-[1+_] zero))    = refl
relAbsRel (relativePitch zero    , octave (-[1+_] (suc n))) = {!!}
relAbsRel (relativePitch (suc n) , octave (+_     zero))    = {!!}
relAbsRel (relativePitch (suc n) , octave (+_     (suc o))) = {!!}
relAbsRel (relativePitch (suc n) , octave (-[1+_] zero))    = {!!}
relAbsRel (relativePitch (suc n) , octave (-[1+_] (suc o))) = {!!}
-}
