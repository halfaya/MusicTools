{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Environment (getArgs)

import Data.List (intercalate)
import Data.Maybe (fromMaybe)

import Midi
import Serial
import Smt
import Xml

run :: String -> [String] -> IO String
run "writeXML" args = do
  writeFile (head args) test4
  return ""
run "readXML" args = do
  s <- readFile (head args)
  let ms   = xmlToMeasures s
  return $ showMeasures ms
run "solve" (vs : cs) = do
  let vars = lines vs
  let constraints = map bdserialTop cs
  res <- solveConstraints vars constraints
  return $ intercalate " " (map (show . fromMaybe 0) res)
run c _ = return $ "UNKNOWN COMMAND: " ++ c

main :: IO ()
main = do
  args <- getArgs
  result <- run (head args) (tail args)
  putStr result
