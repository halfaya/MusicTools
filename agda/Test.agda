module Test where

open import Pitch
open import Interval
open import Counterpoint

open import Data.Vec using (Vec; []; _∷_; zip)
open import Data.Fin using (zero; suc)

open import Relation.Binary.PropositionalEquality using (refl)

-- Last five notes of Yamanote melody
cantusFirmus : Vec Pitch 5
cantusFirmus = c 5 ∷ e 5 ∷ g 5 ∷ d 6 ∷ c 6 ∷ []

counterpoint : Vec Interval 5
counterpoint = maj10 ∷ min10 ∷ per8 ∷ maj6 ∷ per8 ∷ []

firstSpecies : Counterpoint 3
firstSpecies = zip cantusFirmus counterpoint

testCorrect : FirstSpecies firstSpecies
testCorrect = fs firstSpecies
                 (λ { zero → refl ;
                      (suc zero) → refl ;
                      (suc (suc zero)) → refl ;
                      (suc (suc (suc zero))) → refl ;
                      (suc (suc (suc (suc zero)))) → refl })
                 (λ { zero → refl ;
                      (suc zero) → refl ;
                      (suc (suc zero)) → refl ;
                      (suc (suc (suc zero))) → refl})
                 refl
