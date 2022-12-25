{-# LANGUAGE ScopedTypeVariables #-}

module Xml where

import Data.List (transpose, intercalate)
import Text.XML.Light

qn :: String -> QName
qn s = QName { qName = s, qURI = Nothing, qPrefix = Nothing }

attr :: String -> Element -> String
attr s e = case findAttrBy (\q -> qName q == s) e of
  Just x  -> x
  Nothing -> "NOTFOUND"

children :: String -> Element -> [Element]
children s = filterChildrenName (\q -> qName q == s)

child :: String -> Element -> Element
child s e = head (children s e)

cval :: String -> Element -> String
cval s e = strContent (child s e)

type Step   = String
type Octave = String
type Voice  = String
type MNum   = String

type Pitch    = (Step, Octave)
type Note     = (Voice, Pitch)
type Measure  = (MNum, [Note])

pitch :: Element -> Pitch
pitch e = (cval "step" e , cval "octave" e)

showPitch :: Pitch -> String
showPitch (s,o) = s ++ "♮" ++ o

note :: Element -> Note
note e = (cval "voice" e , pitch (child "pitch" e))

showNote :: Note -> String
showNote (_,p) = showPitch p

measure :: Element -> Measure
measure e = (attr "number" e , map note (children "note" e))

measures :: Element -> [Measure]
measures e = map measure (children "measure" e)

part :: [Content] -> Element
part xs = child "part" (onlyElems xs !! 1)

splitByVoice :: [Note] -> [[Note]]
splitByVoice []              = []
splitByVoice xs@((v, _) : _) =
  let (ys, zs) = span (\n -> fst n == v) xs
  in ys : splitByVoice zs

-- Reorganize measures so that notes in each voice are put together
reorg :: [Measure] -> [[Note]]
reorg ms = map concat (transpose (map (splitByVoice . snd) ms))

showMeasures :: [Measure] -> String
showMeasures ms = intercalate "\n" (map (\ns -> intercalate " " (map showNote ns)) (reorg ms))

xmlToMeasures :: String -> [Measure]
xmlToMeasures = measures . part . parseXML
