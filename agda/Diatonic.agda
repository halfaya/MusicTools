{-# OPTIONS --without-K #-}

module Diatonic where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Nat.DivMod using (_mod_)
open import Data.Vec using (Vec; []; _∷_; head; foldl; take; reverse)

open import Function using (_∘_)

open import Pitch

data Accidental : Set where
  𝄫 : Accidental
  ♭ : Accidental
  ♮ : Accidental
  ♯ : Accidental
  𝄪 : Accidental

-- pitch class letter name with accidental
data PC : Set where
  A : Accidental → PC
  B : Accidental → PC
  C : Accidental → PC
  D : Accidental → PC
  E : Accidental → PC
  F : Accidental → PC
  G : Accidental → PC

-- Accidental modifier. To stay in ℕ we map 𝄫 to 0.
accMod : Accidental → ℕ
accMod 𝄫 = 0
accMod ♭ = 1
accMod ♮ = 2
accMod ♯ = 3
accMod 𝄪 = 4

flatten : Accidental → Accidental
flatten 𝄫 = 𝄫 -- should make this an error
flatten ♭ = 𝄫
flatten ♮ = ♭
flatten ♯ = ♮
flatten 𝄪 = ♯

sharpen : Accidental → Accidental
sharpen 𝄫 = ♭
sharpen ♭ = ♮
sharpen ♮ = ♯
sharpen ♯ = 𝄪
sharpen 𝄪 = 𝄪 -- should make this an error

-- Convert raw PC letter to ℕ (in range [0,11]); C normalized to 0
letter→ℕ : PC → ℕ
letter→ℕ (A _) = 9
letter→ℕ (B _) = 11
letter→ℕ (C _) = 0
letter→ℕ (D _) = 2
letter→ℕ (E _) = 4
letter→ℕ (F _) = 5
letter→ℕ (G _) = 7

accidental : PC → Accidental
accidental (A x) = x
accidental (B x) = x
accidental (C x) = x
accidental (D x) = x
accidental (E x) = x
accidental (F x) = x
accidental (G x) = x

-- Convert PC to PitchClass with C♮ normalized to 0.
pcToC : PC → PitchClass
pcToC pc = pitchClass ((letter→ℕ pc + accMod (accidental pc) + 10) mod 12)

data Key : Set where
  key : PC → Key

data Mode : Set where
  major : Mode
  minor : Mode

data Step : Set where
  half  : Step
  whole : Step

stepUp : Step → PC → PC

stepUp half  (A x) = B (flatten x)
stepUp half  (B x) = C x
stepUp half  (C x) = D (flatten x)
stepUp half  (D x) = E (flatten x)
stepUp half  (E x) = F x
stepUp half  (F x) = G (flatten x)
stepUp half  (G x) = A (flatten x)

stepUp whole (A x) = B x
stepUp whole (B x) = C (sharpen x)
stepUp whole (C x) = D x
stepUp whole (D x) = E x
stepUp whole (E x) = F (sharpen x)
stepUp whole (F x) = G x
stepUp whole (G x) = A x

scaleSteps : Mode → Vec Step diatonicScaleSize
scaleSteps major = whole ∷ whole ∷ half ∷ whole ∷ whole ∷ whole ∷ half ∷ []
scaleSteps minor = whole ∷ half ∷ whole ∷ whole ∷ half ∷ whole ∷ whole ∷ []

scaleNotes : Key → Mode → Vec PC diatonicScaleSize
scaleNotes (key pc) m =
  let f : {n : ℕ} → Vec PC (suc n) → Step → Vec PC (suc (suc n))
      f pcs step = stepUp step (head pcs) ∷ pcs
  in reverse (foldl (Vec PC ∘ suc) f (pc ∷ []) (take 6 (scaleSteps m)))

cc = scaleNotes (key (C ♭)) minor

