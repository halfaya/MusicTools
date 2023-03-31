{-# OPTIONS --without-K --safe #-}

module Parse where

open import Prelude

open import Data.Nat.Show using (readMaybe)

open import Pitch using (Octave)
open import Symbolic

readNat : String → ℕ
readNat s with readMaybe 10 s
... | just n  = n
... | nothing = 0

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

parseOctave : Char -> Octave
parseOctave c = char→ℕ c ∸ char→ℕ '0'

parseSPitch : List Char → SPitch
parseSPitch (l ∷ a ∷ o ∷ _) = sp (nn (parseLetter l) (parseAcc a)) (parseOctave o)
parseSPitch _               = sp C♮ 0 -- default in case of parse failure

parseSNote : List Char → SNote
parseSNote (l ∷ a ∷ o ∷ d) = sn (!! (parseSPitch (l ∷ a ∷ o ∷ []))) (readNat (fromChars d))
parseSNote _               = sn (!! (sp C♮ 0)) 8  -- default in case of parse failure

parseVoice : String → List SNote
parseVoice s = map (parseSNote ∘ toChars) (words s)

parseMusic : String → List (List SNote)
parseMusic s = map parseVoice (lines s)
