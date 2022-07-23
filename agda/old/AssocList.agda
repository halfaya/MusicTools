{-# OPTIONS --cubical --safe #-}

module AssocList where

open import Cubical.Core.Everything using (Type)

open import Data.Bool       using (Bool; false; true; _∨_; _∧_)
open import Data.List       using (List; []; _∷_; foldr)
open import Data.Product    using (_×_; _,_; proj₂)

open import Function        using (_∘_)

AList : (A B : Type) → Type
AList A B = List (A × List B)

-- Does not deduplicate in list of B.
insert : {A B : Type} → (A → A → Bool) → A × B → AList A B → AList A B
insert eq (a , b) []       = (a , b ∷ []) ∷ [] 
insert eq (a , b) ((a' , bs) ∷ xs) with eq a a'
... | false = (a' , bs)     ∷ insert eq (a , b) xs
... | true  = (a' , b ∷ bs) ∷ xs

lookup : {A B : Type} → (A → A → Bool) → A → AList A B → List B
lookup eq _ []               = []
lookup eq a ((a' , bs) ∷ xs) with eq a a'
... | false = lookup eq a xs
... | true  = bs
