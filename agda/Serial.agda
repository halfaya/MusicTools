{-# OPTIONS --without-K --safe #-}

module Serial where

open import Prelude hiding (#_; _==_; _+_; _mod_; _-_; if_then_else_; _∧_; _∨_; _≤_)

open import Expr

cat3 : String → String → String → String
cat3 x y z = x ++s y ++s z

-- Serialize IExpr and BExpr as s-expressions.
iserial : IExpr → String
bserial : BExpr → String

iserial (# x)    = "#" ++s showℤ x
iserial (var x)  = "'" ++s x ++s "'"
iserial (x + y) = cat3 "+" (iserial x) (iserial y) 
iserial (x - y) = cat3 "-" (iserial x) (iserial y) 
iserial (x % y) = cat3 "%" (iserial x) (iserial y) 
iserial (if x then y else z) = cat3 "I" (bserial x) (iserial y ++s iserial z)

bserial false    = "F"
bserial true     = "T"
bserial (x ∧ y)  = cat3 "∧" (bserial x) (bserial y) 
bserial (x ∨ y)  = cat3 "∨" (bserial x) (bserial y) 
bserial (¬ x)    = "¬" ++s bserial x
bserial (x == y) = cat3 "=" (iserial x) (iserial y) 
bserial (x ≠ y)  = cat3 "≠" (iserial x) (iserial y) 
bserial (x < y)  = cat3 "<" (iserial x) (iserial y) 
bserial (x ≤ y)  = cat3 "≤" (iserial x) (iserial y) 
bserial (x > y)  = cat3 ">" (iserial x) (iserial y) 
bserial (x ≥ y)  = cat3 "≥" (iserial x) (iserial y) 
