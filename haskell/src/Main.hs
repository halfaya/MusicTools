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
  let notes    = parseNotes (tail args)
  let measures = deorg 2 notes -- for now assume first-species half notes
  let xml      = measuresToXml measures
  let score    = ppScore xml
  writeFile (head args) score
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

----------
-- Test

test =
  "C♮58 D♮58 E♮58 F♮58 E♮58 D♮58 C♮58 B♮48 D♮58 E♮58 D♮58 D♮58 C♮58 C♮58 D♮58 C♮58" :
  "G♮48 D♮48 C♮48 A♮38 A♮48 B♮48 A♮48 G♮48 F♮48 G♮48 B♮48 B♮38 A♮48 A♮48 G♮48 G♮48" :
  "E♮38 B♮38 A♮38 F♮38 C♮48 D♮48 E♮48 E♮48 A♮38 G♮38 D♮48 G♮38 E♮38 F♮48 B♮38 E♮38" :
  "C♮38 B♮28 C♮38 D♮38 C♮38 B♮28 C♮38 E♮38 F♮38 E♮38 B♮28 B♮28 C♮38 A♮28 B♮28 C♮38" : []

runt :: IO String
runt  = run "writeXML" ("/Users/leo/Music/XML/Test1out.xml" : test)

runt2 :: IO String
runt2 = run "readXML" ["/Users/leo/Music/XML/Test1.xml"]
