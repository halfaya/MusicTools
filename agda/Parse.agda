{-# OPTIONS --without-K --safe #-}

module Parse where

open import Prelude

open import Pitch using (Octave)
open import Symbolic

parseLetter : Char → Letter
parseLetter c =
  if c ==c 'C' then C
  else if c ==c 'D' then D
  else if c ==c 'E' then E
  else if c ==c 'F' then F
  else if c ==c 'G' then G
  else if c ==c 'A' then A
  else B

parseAcc : Char → Acc
parseAcc c =
  if c ==c '𝄫' then 𝄫
  else if c ==c '♭' then ♭
  else if c ==c '♮' then ♮
  else if c ==c '♯' then ♯
  else 𝄪

-- Need to add one to the octave since the MIDI standard is
-- middle C = C5, but the MusicXML standard is C4
parseOctave : Char -> Octave
parseOctave c = suc (char→ℕ c ∸ char→ℕ '0')

parseNPitch : List Char → NPitch
parseNPitch (l ∷ a ∷ o ∷ _) = np (nn (parseLetter l) (parseAcc a)) (parseOctave o)
parseNPitch _               = np C♮ 0 -- default in case of parse failure

parseVoice : String → List NPitch
parseVoice s = map (parseNPitch ∘ toChars) (words s)

parseMusic : String → List (List NPitch)
parseMusic s = map parseVoice (lines s)
