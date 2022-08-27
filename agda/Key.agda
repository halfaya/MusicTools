{-# OPTIONS --erased-cubical --safe #-}

module Key where

open import Prelude

open import Pitch

-- Accidentals
data Acc : Type where
  ♭ : Acc
  ♮ : Acc
  ♯ : Acc

showAcc : Acc → String
showAcc ♭ = "♭"
showAcc ♮ = ""
showAcc ♯ = "♯"

data NoteBase : Type where
  C : NoteBase  
  D : NoteBase  
  E : NoteBase  
  F : NoteBase  
  G : NoteBase  
  A : NoteBase  
  B : NoteBase

showNoteBase : NoteBase → String
showNoteBase C = "C"
showNoteBase D = "D"
showNoteBase E = "E"
showNoteBase F = "F"
showNoteBase G = "G"
showNoteBase A = "A"
showNoteBase B = "B"

NoteName : Type
NoteName = NoteBase × Acc

showNoteName : NoteName → String
showNoteName (n , a) = showNoteBase n ++s showAcc a

-- Note names associated with each chromatic step in a key, starting with note C
-- There is some arbitrariness involved.
keyNoteNames : Key → Vec NoteName s12
keyNoteNames C =
  (C , ♮) ∷ (C , ♯) ∷ (D , ♮) ∷ (E , ♭) ∷ (E , ♮) ∷ (F , ♮) ∷
  (F , ♯) ∷ (G , ♮) ∷ (A , ♭) ∷ (A , ♮) ∷ (B , ♭) ∷ (B , ♮) ∷ []
keyNoteNames F = 
  (C , ♮) ∷ (C , ♯) ∷ (D , ♮) ∷ (E , ♭) ∷ (E , ♮) ∷ (F , ♮) ∷
  (F , ♯) ∷ (G , ♮) ∷ (A , ♭) ∷ (A , ♮) ∷ (B , ♭) ∷ (B , ♮) ∷ []
keyNoteNames G =
  (C , ♮) ∷ (C , ♯) ∷ (D , ♮) ∷ (E , ♭) ∷ (E , ♮) ∷ (F , ♮) ∷
  (F , ♯) ∷ (G , ♮) ∷ (G , ♯) ∷ (A , ♮) ∷ (B , ♭) ∷ (B , ♮) ∷ []

