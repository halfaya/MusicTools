module Properties where

open import Data.Fin
open import Data.Nat
open import Data.Integer
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Pitch

absRelAbs : (n : Pitch) → (relativeToAbsolute ∘ absoluteToRelative) n ≡ n
absRelAbs (pitch (+_     zero))    = refl
absRelAbs (pitch (+_     (suc n))) = let x = absRelAbs (pitch (+ n)) in {!!}
absRelAbs (pitch (-[1+_] zero))    = refl
absRelAbs (pitch (-[1+_] (suc n))) = {!!}

relAbsRel : (n : PitchOctave) → (absoluteToRelative ∘ relativeToAbsolute) n ≡ n
relAbsRel (relativePitch zero    , octave (+_     zero))    = refl
relAbsRel (relativePitch zero    , octave (+_     (suc n))) = {!!}
relAbsRel (relativePitch zero    , octave (-[1+_] zero))    = refl
relAbsRel (relativePitch zero    , octave (-[1+_] (suc n))) = {!!}
relAbsRel (relativePitch (suc n) , octave (+_     zero))    = {!!}
relAbsRel (relativePitch (suc n) , octave (+_     (suc o))) = {!!}
relAbsRel (relativePitch (suc n) , octave (-[1+_] zero))    = {!!}
relAbsRel (relativePitch (suc n) , octave (-[1+_] (suc o))) = {!!}
