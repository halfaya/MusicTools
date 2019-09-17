{-# OPTIONS --without-K #-}

module SecondSpecies where

open import Music hiding (transpose)
open import Note hiding (transpose)
open import Pitch
open import Counterpoint

open import Data.Bool hiding (_≟_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_;  -[1+_])
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

