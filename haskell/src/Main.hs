{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Environment (getArgs)

import Midi
import Xml

run :: String -> [String] -> IO String
run "readXML" args = do
  s <- readFile (head args)
  let ms   = xmlToMeasures s
  return $ showMeasures ms
run c _ = return $ "UNKNOWN COMMAND: " ++ c

main :: IO ()
main = do
  args <- getArgs
  result <- run (head args) (tail args)
  putStrLn result
