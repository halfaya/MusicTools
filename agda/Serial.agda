{-# OPTIONS --without-K --safe #-}

module Serial where

open import Prelude hiding (#_; _==_; _+_; _mod_; _-_; if_then_else_; _∧_; _∨_; _≤_)

open import Expr

paren : String → String → String → String
paren x y z = "(" ++s x ++s y ++s z ++s ")"

-- Serialize IExpr and BExpr as s-expressions.
iserial : IExpr → String
bserial : BExpr → String

iserial (# x)    = "#" ++s showℤ x
iserial (var x)  = "'" ++s x ++s "'"
iserial (x + y) = paren "+" (iserial x) (iserial y) 
iserial (x - y) = paren "-" (iserial x) (iserial y) 
iserial (x % y) = paren "%" (iserial x) (iserial y) 
iserial (if x then y else z) = paren "I" (bserial x) (iserial y ++s iserial z)

bserial false    = "F"
bserial true     = "T"
bserial (x ∧ y)  = paren "∧" (bserial x) (bserial y) 
bserial (x ∨ y)  = paren "∨" (bserial x) (bserial y) 
bserial (¬ x)    = "(" ++s "¬" ++s bserial x ++s ")"
bserial (x == y) = paren "=" (iserial x) (iserial y) 
bserial (x ≠ y)  = paren "≠" (iserial x) (iserial y) 
bserial (x < y)  = paren "<" (iserial x) (iserial y) 
bserial (x ≤ y)  = paren "≤" (iserial x) (iserial y) 
bserial (x > y)  = paren ">" (iserial x) (iserial y) 
bserial (x ≥ y)  = paren "≥" (iserial x) (iserial y) 
