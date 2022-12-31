{-# LANGUAGE ScopedTypeVariables #-}

module Xml where

import Data.List (transpose, intercalate, intersperse, groupBy)
import Data.List.Split (chunksOf)
import Text.XML.Light
import Text.XML.Light.Output

xattr :: String -> String -> Attr
xattr k v = Attr {attrKey = unqual k, attrVal = v}

numattr :: String -> Attr
numattr = xattr "number"

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

type Duration = Int
type Step     = String
type Octave   = String
type Voice    = String
type MNum     = String

type Pitch    = (Step, Octave)
type Note     = (Voice, Duration, Pitch)
type Measure  = (MNum, [Note])

pitch :: Element -> Pitch
pitch e = (cval "step" e , cval "octave" e)

xpitch :: Pitch -> Element
xpitch (s,o) = unode "pitch" [unode "step" s, unode "octave" o]

showPitch :: Pitch -> String
showPitch (s,o) = s ++ "♮" ++ o

-- Does not yet handle accidentals.
parsePitch :: String -> Pitch
parsePitch (s : o : []) = (s :[] , o : [])
parsePitch (s : a : o : []) = (s :[] , o : []) -- discards accidental

note :: Element -> Note
note e = (cval "voice" e , read (cval "duration" e), pitch (child "pitch" e))

noteStaff :: Voice -> String
noteStaff v = if v == "3" || v == "4" then "2" else "1"

noteStem :: Voice -> String
noteStem v = if v == "2" || v == "4" then "down" else "up"

xnote :: Note -> Element
xnote (v,d,p) = unode "note"
  [xpitch p,
   unode "duration" (show d),
   unode "voice" v,
   unode "type" "half",
   unode "stem" (noteStem v),
   unode "staff" (noteStaff v)]

showNote :: Note -> String
showNote (_,_,p) = showPitch p

parseNote :: Voice -> String -> Note
parseNote v s = (v, 8, parsePitch s)

-- List of space-separated notes.
parseNotesV :: Voice -> String -> [Note]
parseNotesV v s = map (parseNote v) (words s)

parseNotes :: [String] -> [[Note]]
parseNotes xs = map (\(i,s) -> parseNotesV (show i) s) (zip [1..] xs)

measure :: Element -> Measure
measure e = (attr "number" e , map note (children "note" e))

measures :: Element -> [Measure]
measures e = map measure (children "measure" e)

xclef :: String -> Element
xclef num =
  let (s , l) = if num == "2" then ("F", "4") else ("G", "2")
  in unode "clef" ([numattr num], [unode "sign" s, unode "line" l])

xkey :: String -> Element
xkey num = unode "key" ([numattr num], [unode "fifths" "0", unode "mode" "major"])

xtime :: Element
xtime = unode "time" [unode "beats" "4", unode "beat-type" "4"]


measureAttributes :: Element
measureAttributes =
  unode "attributes"
  [unode "divisions" "4",
   xkey "1",
   xkey "2",
   xtime,
   unode "staves" "2",
   xclef "1",
   xclef "2"]

backup :: Element
backup = unode "backup" (unode "duration" "16")

part :: [Content] -> Element
part xs = child "part" (onlyElems xs !! 1)

splitByVoice :: [Note] -> [[Note]]
splitByVoice = groupBy (\(v,_,_) (w,_,_) -> v == w)

-- Reorganize measures so that notes in each voice are put together.
-- Assumes voice ordering in each measure is the same.
reorg :: [Measure] -> [[Note]]
reorg ms = map concat (transpose (map (splitByVoice . snd) ms))

-- Reorganize list of voices of notes into measures.
deorg :: Int -> [[Note]] -> [Measure]
deorg notesPerMeasure nss =
  let xss = map (chunksOf notesPerMeasure) nss
      yss = map concat (transpose xss)
  in map (\(mn,ns) -> (show mn, ns)) (zip [1..] yss)

showMeasures :: [Measure] -> String
showMeasures ms = intercalate "\n" (map (\ns -> intercalate " " (map showNote ns)) (reorg ms))

xmlToMeasures :: String -> [Measure]
xmlToMeasures = measures . part . parseXML

xmeasure :: Measure -> Element
xmeasure (mn, notes) = unode "measure"
  ([numattr mn],
   (if mn == "1" then [measureAttributes] else []) ++
   intercalate [backup] (map (map xnote) (splitByVoice notes)))

xscore :: Element -> Element
xscore part = unode "score-partwise"
  ([xattr "version" "3.1"],
   [unode "work" (unode "work-title" "Test"),
    unode "part-list" (unode "score-part" ([xattr "id" "P1"], [unode "part-name" "Piano"])),
    part])

measuresToXml :: [Measure] -> Element
measuresToXml ms = xscore (unode "part"
  ([xattr "id" "P1"], map xmeasure ms))

header :: String
header =
  "<?xml version='1.0' encoding='UTF-8' standalone='no'?>\n\
  \<!DOCTYPE score-partwise PUBLIC '-//Recordare//DTD MusicXML 3.1 Partwise//EN' 'http://www.musicxml.org/dtds/partwise.dtd'>\n"

ppScore :: Element -> String
ppScore e = header ++ ppElement e

-----

test =
  "C5 E5 G5 F5 E5 C5 A5 F5 G5 E5 D5 C5" :
  "G4 C5 B4 A4 C5 A4 F4 A4 E5 G4 G4 G4" :
  "E4 E4 E4 F4 G3 C4 A3 F4 E4 E4 B3 C4" : []

test1 = parseNotes test
test2 = deorg 2 test1
test3 = measuresToXml test2

test4 = ppScore test3
