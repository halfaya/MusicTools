{-# OPTIONS --erased-cubical #-}

module Smt where

open import Cubical.Core.Everything using (Type)

open import Agda.Builtin.String using (String)
open import Data.List using (List)
open import Data.Integer using (ℤ)

open import Expr

infix 10 #_
infixr 9 ¬_
infixl 8 _+_ _-_
infix  7 _==_ _≠_ _<_ _≤_
infixr 6 _∧_
infixr 5 _∨_

-- This duplication of data types is necessary due
-- to the restriction that COMPILE GHC datatypes
-- can use only types defined in the same module.

data HMaybe (A : Type) : Type where
  nothing : HMaybe A
  just    : A → HMaybe A

data HIExpr : Type where
  #_ : ℤ → HIExpr
  var   : String → HIExpr
  _+_ : HIExpr → HIExpr → HIExpr
  _-_ : HIExpr → HIExpr → HIExpr

data HBExpr : Type where
  false : HBExpr
  true  : HBExpr
  _==_  : HIExpr → HIExpr → HBExpr
  _≠_   : HIExpr → HIExpr → HBExpr
  _<_   : HIExpr → HIExpr → HBExpr
  _≤_   : HIExpr → HIExpr → HBExpr
  _∧_   : HBExpr → HBExpr → HBExpr
  _∨_   : HBExpr → HBExpr → HBExpr
  ¬_    : HBExpr → HBExpr

I→HIExpr : IExpr → HIExpr
I→HIExpr (# x)   = # x
I→HIExpr (var x) = var x
I→HIExpr (x + y) = I→HIExpr x + I→HIExpr y
I→HIExpr (x - y) = I→HIExpr x - I→HIExpr y

B→HBExpr : BExpr → HBExpr
B→HBExpr false    = false
B→HBExpr true     = true
B→HBExpr (x == y) = I→HIExpr x == I→HIExpr y
B→HBExpr (x ≠ y)  = I→HIExpr x ≠ I→HIExpr y
B→HBExpr (x < y)  = I→HIExpr x < I→HIExpr y
B→HBExpr (x ≤ y)  = I→HIExpr x ≤ I→HIExpr y
B→HBExpr (x ∧ y)  = B→HBExpr x ∧ B→HBExpr y
B→HBExpr (x ∨ y)  = B→HBExpr x ∨ B→HBExpr y
B→HBExpr (¬ x)    = ¬ B→HBExpr x

{-# FOREIGN GHC
  import Data.SBV
  import Data.Text (Text, unpack)
  import System.IO.Unsafe (unsafePerformIO)

  data IExpr =
    Const Integer    |
    Var Text         |
    Plus IExpr IExpr |
    Minus IExpr IExpr
  data BExpr =
    BFalse            |
    BTrue             |
    BEq IExpr IExpr   |
    BNeq IExpr IExpr  |
    BLt IExpr IExpr   |
    BLe IExpr IExpr   |
    BAnd BExpr BExpr  |
    BOr BExpr BExpr   |
    BNot BExpr

  compileIExpr :: IExpr -> Symbolic SInt8
  compileIExpr (Const n) = return $ literal (fromInteger n)
  compileIExpr (Var   s) = free (unpack s)
  compileIExpr (Plus a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c + d
  compileIExpr (Minus a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c - d

  compileBExpr :: BExpr -> Symbolic SBool
  compileBExpr BFalse = return $ sFalse
  compileBExpr BTrue  = return $ sTrue
  compileBExpr (BEq a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c .== d
  compileBExpr (BNeq a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c ./= d
  compileBExpr (BLt a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c .< d
  compileBExpr (BLe a b) = do
    c <- compileIExpr a
    d <- compileIExpr b
    return $ c .<= d
  compileBExpr (BAnd a b) = do
    c <- compileBExpr a
    d <- compileBExpr b
    return $ c .&& d
  compileBExpr (BOr a b) = do
    c <- compileBExpr a
    d <- compileBExpr b
    return $ c .|| d
  compileBExpr (BNot a) = do
    c <- compileBExpr a
    return $ sNot c

  getResults :: [Text] -> SatResult -> [Maybe Integer]
  getResults xs res = map (flip getModelValue res . unpack) xs

  runSat :: [BExpr] -> IO SatResult
  runSat xs = sat $ do
    bs <- sequence $ map compileBExpr xs
    solve bs

  solveConstraints :: [Text] -> [BExpr] -> [Maybe Integer]
  solveConstraints xs bs =
    getResults xs (unsafePerformIO (runSat bs))
#-}

postulate
  solveConstraints : List String → List HBExpr → List (HMaybe ℤ)

{-# COMPILE GHC HMaybe = data Maybe (Nothing | Just) #-}
{-# COMPILE GHC HIExpr = data IExpr (Const | Var | Plus | Minus) #-}
{-# COMPILE GHC HBExpr = data BExpr (BFalse | BTrue | BEq | BNeq | BLt | BLe | BAnd | BOr | BNot) #-}

{-# COMPILE GHC solveConstraints = solveConstraints #-}
