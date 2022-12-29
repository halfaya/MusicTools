{-# LANGUAGE ScopedTypeVariables #-}

module Smt where

import Data.SBV

import Expr

type VarTable = [(String, SInt8)]

makeVarTable :: [String] -> Symbolic VarTable
makeVarTable xs = do
  vs <- mapM free xs
  return $ zip xs vs

lookupVar :: String -> VarTable -> SInt8
lookupVar t []           = error ("lookup: unknown symbol " ++ t)
lookupVar t ((u,x) : xs) = if t == u then x else lookupVar t xs

compileIExpr :: VarTable -> IExpr -> SInt8
compileIExpr vt (Const n)   = literal n
compileIExpr vt (Var   s)   = lookupVar s vt
compileIExpr vt (Plus a b)  = compileIExpr vt a + compileIExpr vt b
compileIExpr vt (Minus a b) = compileIExpr vt a - compileIExpr vt b
compileIExpr vt (Mod a b)   = compileIExpr vt a `sMod` compileIExpr vt b
compileIExpr vt (Ite b a c) = ite (compileBExpr vt b) (compileIExpr vt a) (compileIExpr vt c)

compileBExpr :: VarTable -> BExpr -> SBool
compileBExpr vt BFalse     = sFalse
compileBExpr vt BTrue      = sTrue
compileBExpr vt (BEq a b)  = compileIExpr vt a .== compileIExpr vt b
compileBExpr vt (BNeq a b) = compileIExpr vt a ./= compileIExpr vt b
compileBExpr vt (BLt a b)  = compileIExpr vt a .< compileIExpr vt b
compileBExpr vt (BLe a b)  = compileIExpr vt a .<= compileIExpr vt b
compileBExpr vt (BGt a b)  = compileIExpr vt a .> compileIExpr vt b
compileBExpr vt (BGe a b)  = compileIExpr vt a .>= compileIExpr vt b
compileBExpr vt (BAnd a b) = compileBExpr vt a .&& compileBExpr vt b
compileBExpr vt (BOr a b)  = compileBExpr vt a .|| compileBExpr vt b
compileBExpr vt (BNot a)   = sNot (compileBExpr vt a)

getResults :: [String] -> IO SatResult -> IO [Maybe Integer]
getResults xs res = do
  r <- res
  return $ map (flip getModelValue r) xs

runSat :: [String] -> [BExpr] -> IO SatResult
runSat ts xs = satWith z3 {verbose=False} $ do -- change verbose=True to debug
  vt <- makeVarTable ts
  let bs = map (compileBExpr vt) xs
  solve bs

solveConstraints :: [String] -> [BExpr] -> IO [Maybe Integer]
solveConstraints ts bs = getResults ts (runSat ts bs)
