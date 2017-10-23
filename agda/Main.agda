module Main where

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate
  putStrLn : String → IO Unit

{-# COMPILE GHC putStrLn = Text.putStrLn #-}

main : IO Unit
main = putStrLn "Hello, World!"
