{-# OPTIONS --erased-cubical #-}

module Smt where

open import Cubical.Core.Everything using (Type)

open import Agda.Builtin.String using (String)
open import Data.List           using (List; map)
open import Data.Integer        using (ℤ)
open import Function            using (_∘_)

open import Expr
open import Constraint using (Constraint; compileConstraint)

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


data HBExpr : Type
B→HBExpr : BExpr → HBExpr

data HIExpr : Type where
  #_            : ℤ → HIExpr
  var           : String → HIExpr
  _+_           : HIExpr → HIExpr → HIExpr
  _-_           : HIExpr → HIExpr → HIExpr
  if_then_else_ : HBExpr → HIExpr → HIExpr → HIExpr

data HBExpr where
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
I→HIExpr (# x)                = # x
I→HIExpr (var x)              = var x
I→HIExpr (x + y)              = I→HIExpr x + I→HIExpr y
I→HIExpr (x - y)              = I→HIExpr x - I→HIExpr y
I→HIExpr (if b then a else c) = if (B→HBExpr b) then (I→HIExpr a) else (I→HIExpr c) 

--B→HBExpr : BExpr → HBExpr
B→HBExpr false    = false
B→HBExpr true     = true
B→HBExpr (x == y) = I→HIExpr x == I→HIExpr y
B→HBExpr (x ≠ y)  = I→HIExpr x ≠ I→HIExpr y
B→HBExpr (x < y)  = I→HIExpr x < I→HIExpr y
B→HBExpr (x ≤ y)  = I→HIExpr x ≤ I→HIExpr y
B→HBExpr (x ∧ y)  = B→HBExpr x ∧ B→HBExpr y
B→HBExpr (x ∨ y)  = B→HBExpr x ∨ B→HBExpr y
B→HBExpr (¬ x)    = ¬ B→HBExpr x

compileConstraints : List Constraint → List HBExpr
compileConstraints = map (B→HBExpr ∘ compileConstraint)


{-# FOREIGN GHC
  import Data.SBV
  import Data.Text (Text, unpack, pack)
  import System.IO.Unsafe (unsafePerformIO)

  data IExpr =
    Const Integer     |
    Var Text          |
    Plus IExpr IExpr  |
    Minus IExpr IExpr |
    Ite BExpr IExpr IExpr
    deriving Show

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
    deriving Show

  type VarTable = [(Text, SInt8)]

  makeVarTable :: [Text] -> Symbolic VarTable
  makeVarTable xs = do
    vs <- mapM (free . unpack) xs
    return $ zip xs vs

  lookupVar :: Text -> VarTable -> SInt8
  lookupVar t []           = error ("lookup: unknown symbol " ++ (unpack t))
  lookupVar t ((u,x) : xs) = if t == u then x else lookupVar t xs

  compileIExpr :: VarTable -> IExpr -> SInt8
  compileIExpr vt (Const n)   = literal (fromInteger n)
  compileIExpr vt (Var   s)   = lookupVar s vt
  compileIExpr vt (Plus a b)  = compileIExpr vt a + compileIExpr vt b
  compileIExpr vt (Minus a b) = compileIExpr vt a + compileIExpr vt b
  compileIExpr vt (Ite b a c) = ite (compileBExpr vt b) (compileIExpr vt a) (compileIExpr vt c)

  compileBExpr :: VarTable -> BExpr -> SBool
  compileBExpr vt BFalse     = sFalse
  compileBExpr vt BTrue      = sTrue
  compileBExpr vt (BEq a b)  = compileIExpr vt a .== compileIExpr vt b
  compileBExpr vt (BNeq a b) = compileIExpr vt a ./= compileIExpr vt b
  compileBExpr vt (BLt a b)  = compileIExpr vt a .< compileIExpr vt b
  compileBExpr vt (BLe a b)  = compileIExpr vt a .<= compileIExpr vt b
  compileBExpr vt (BAnd a b) = compileBExpr vt a .&& compileBExpr vt b
  compileBExpr vt (BOr a b)  = compileBExpr vt a .|| compileBExpr vt b
  compileBExpr vt (BNot a)   = sNot (compileBExpr vt a)

  getResults :: [Text] -> SatResult -> [Maybe Integer]
  getResults xs res = map (flip getModelValue res . unpack) xs

  runSat :: [Text] -> [BExpr] -> IO SatResult
  runSat ts xs = satWith z3 {verbose=True} $ do
    vt <- makeVarTable ts
    let bs = map (compileBExpr vt) xs
    solve bs

  solveConstraints :: [Text] -> [BExpr] -> [Maybe Integer]
  solveConstraints ts bs = getResults ts (unsafePerformIO (runSat ts bs))
#-}

postulate
  solveConstraints : List String → List HBExpr → List (HMaybe ℤ)

{-# COMPILE GHC HMaybe = data Maybe (Nothing | Just) #-}
{-# COMPILE GHC HIExpr = data IExpr (Const | Var | Plus | Minus | Ite) #-}
{-# COMPILE GHC HBExpr = data BExpr (BFalse | BTrue | BEq | BNeq | BLt | BLe | BAnd | BOr | BNot) #-}

{-# COMPILE GHC solveConstraints = solveConstraints #-}