{-# OPTIONS --erased-cubical #-}

module Smt where

open import Cubical.Core.Everything using (Type)

open import Agda.Builtin.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)

data Maybe (A : Type) : Type where
  nothing : Maybe A
  just    : A → Maybe A

data IExpr : Type where
  const : ℕ → IExpr
  var   : String → IExpr

data BExpr : Type where
  eq : IExpr → IExpr → BExpr

{-# FOREIGN GHC
  import Data.SBV
  import Data.Text (Text, unpack)
  import System.IO.Unsafe (unsafePerformIO)

  data IExpr = Const Integer | Var Text
  data BExpr = Eq IExpr IExpr

  compileIExpr :: IExpr -> Symbolic SInt8
  compileIExpr (Const n) = return $ literal (fromInteger n)
  compileIExpr (Var   s) = free (unpack s)

  compileBExpr :: BExpr -> Symbolic SBool
  compileBExpr (Eq a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c .== d

  getPitches :: [Text] -> SatResult -> [Maybe Integer]
  getPitches xs res = map (flip getModelValue res . unpack) xs

  runSat :: [BExpr] -> IO SatResult
  runSat xs = sat $ do
    bs <- sequence $ map compileBExpr xs
    solve bs

  solveConstraints :: [Text] -> [BExpr] -> [Maybe Integer]
  solveConstraints xs bs =
    getPitches xs (unsafePerformIO (runSat bs))
#-}

postulate
  solveConstraints : List String → List BExpr → List (Maybe ℕ)

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}
{-# COMPILE GHC IExpr = data IExpr (Const | Var) #-}
{-# COMPILE GHC BExpr = data BExpr (Eq) #-}

{-# COMPILE GHC solveConstraints = solveConstraints #-}
