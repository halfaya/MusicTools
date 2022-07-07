{-# OPTIONS --erased-cubical #-}

module Smt where

open import Cubical.Core.Everything using (Type)

open import Agda.Builtin.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)

data Maybe (A : Type) : Type where
  nothing : Maybe A
  just    : A → Maybe A
  
{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

{-# FOREIGN GHC
  import Data.SBV
  import Data.Text (Text, unpack)
  import System.IO.Unsafe (unsafePerformIO)

  getPitches' :: [String] -> SatResult -> [Maybe Integer]
  getPitches' xs res = map (\x -> getModelValue x res) xs

  getPitches :: [String] -> IO SatResult -> [Maybe Integer]
  getPitches xs res = unsafePerformIO (fmap (getPitches' xs) res)

  runSat :: IO SatResult
  runSat= sat $ do
    x <- free "var1" :: Symbolic SInt8
    let b = x .== 13 :: SBool
    solve [b]

  solveConstraintsT :: [Text] -> [Maybe Integer]
  solveConstraintsT = solveConstraints . (map unpack)

  solveConstraints :: [String] -> [Maybe Integer]
  solveConstraints xs = getPitches xs runSat
#-}

postulate
  solveConstraints : List String → List (Maybe ℕ)

{-# COMPILE GHC solveConstraints = solveConstraintsT #-}
