{-# LANGUAGE ScopedTypeVariables #-}

module Serial where

import Data.Char (isDigit)
import Data.SBV (Int8)

import Expr

-- De-serialize IExpr and BExpr as s-expressions.

map1 :: (a -> c) -> (a , b) -> (c , b)
map1 f (a , b) = (f a , b)

map2 :: (b -> c) -> (a , b) -> (a , c)
map2 f (a , b) = (a , f b)

seq2 :: (b -> c -> d) ->
        (a -> (b , a)) ->
        (a -> (c , a)) ->
        a -> (d , a)
seq2 f g h a =
  let (b , a1) = g a
      (c , a2) = h a1
  in (f b c , a2)

seq3 :: (b -> c -> d -> e) ->
        (a -> (b , a)) ->
        (a -> (c , a)) ->
        (a -> (d , a)) ->
        a -> (e , a)
seq3 f g h i a =
  let (b , a1) = g a
      (c , a2) = h a1
      (d , a3) = i a2
  in (f b c d, a3)

readInt8 :: String -> (Int8, String)
readInt8 ('-' : s) = map1 (negate . read) (span isDigit s)
readInt8 s         = map1 read (span isDigit s)

readString :: String -> (String, String)
readString s = map2 tail (span (\c -> c /= '\'') s)

idserial :: String -> (IExpr , String)
idserial ('#' : s)  = map1 Const (readInt8 s)
idserial ('\'' : s) = map1 Var (readString s)
idserial ('+' : s)  = seq2 Plus idserial idserial s
idserial ('-' : s)  = seq2 Minus idserial idserial s
idserial ('%' : s)  = seq2 Mod idserial idserial s
idserial ('I' : s)  = seq3 Ite bdserial idserial idserial s

bdserial :: String -> (BExpr, String)
bdserial ('F' : s) = (BFalse, s)
bdserial ('T' : s) = (BTrue, s)
bdserial ('∧' : s) = seq2 BAnd bdserial bdserial s
bdserial ('∨' : s) = seq2 BOr bdserial bdserial s
bdserial ('¬' : s) = map1 BNot (bdserial s)
bdserial ('=' : s) = seq2 BEq idserial idserial s
bdserial ('≠' : s) = seq2 BNeq idserial idserial s
bdserial ('<' : s) = seq2 BLt idserial idserial s
bdserial ('≤' : s) = seq2 BLe idserial idserial s
bdserial ('>' : s) = seq2 BGt idserial idserial s
bdserial ('≥' : s) = seq2 BGe idserial idserial s

bdserialTop :: String -> BExpr
bdserialTop = fst . bdserial

