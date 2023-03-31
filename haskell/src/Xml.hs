{-# LANGUAGE
  ScopedTypeVariables,
  NamedFieldPuns,
  RecordWildCards,
  OverloadedRecordDot
#-}

module Xml where

import Data.Char (digitToInt)
import Data.List (transpose, intercalate, intersperse, groupBy)
import Data.List.Split (splitOn, chunksOf)
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

child :: String -> Element -> Maybe Element
child s e = case (children s e) of
  []      -> Nothing
  (x : _) -> Just x

-- When you're sure there's a child.
childX :: String -> Element -> Element
childX s e = let (Just x) = (child s e) in x

childR :: [String] -> Element -> Maybe Element
childR []       _ = Nothing
childR [x]      e = child x e
childR (x : xs) e = child x e >>= childR xs

cval :: String -> Element -> String
cval s e = case (child s e) of
  Nothing -> ""
  Just x  -> strContent x

-- d is default value if not found
cvald :: String -> String -> Element -> String
cvald d s e = case (child s e) of
  Nothing -> d
  Just x  -> strContent x

cvalR :: [String] -> Element -> Maybe String
cvalR xs e = fmap strContent (childR xs e)

type Duration = Int
type Step     = String
type Octave   = String
type Alter    = String
type Voice    = String
type MNum     = String

data Pitch = Pitch {
  pStep   :: Step,
  pOctave :: Octave,
  pAlter  :: Alter }
  deriving Show
  
data Note = Note {
  nVoice    :: Voice,
  nDuration :: Duration,
  nPitch    :: Pitch }
  deriving Show

data Measure = Measure {
  mNum   :: MNum,
  mNotes :: [Note] }
  deriving Show

showAlter :: Alter -> String
showAlter "0"  = "♮"
showAlter "-1" = "♭"
showAlter "1"  = "♯"
showAlter s    = s

readAlter :: String -> Alter
readAlter "♮" = "0"
readAlter "♭" = "-1" 
readAlter "♯" = "1"
readAlter s   = s

pitch :: Element -> Pitch
pitch e = Pitch (cval "step" e) (cval "octave" e) (cvald "0" "alter" e)

xpitch :: Pitch -> Element
xpitch Pitch{..} = unode "pitch" [unode "step" pStep,
                                  unode "octave" pOctave,
                                  unode "alter" pAlter]

showPitch :: Pitch -> String
showPitch Pitch{..} = pStep ++ showAlter pAlter ++ pOctave

parsePitch :: String -> Pitch
parsePitch (s : o : [])     = Pitch (s : []) (o : []) "0"
parsePitch (s : a : o : []) = Pitch (s : []) (o : []) (a : [])

note :: Element -> Note
note e = Note (cval "voice" e) (read (cval "duration" e)) (pitch (childX "pitch" e))

noteStaff :: Voice -> String
noteStaff v = if v == "3" || v == "4" then "2" else "1"

noteStem :: Voice -> String
noteStem v = if v == "2" || v == "4" then "down" else "up"

xnote :: Note -> Element
xnote Note{..} = unode "note"
  [xpitch nPitch,
   unode "duration" (show nDuration),
   unode "voice" nVoice,
   unode "type" "half",
   unode "stem" (noteStem nVoice),
   unode "staff" (noteStaff nVoice)]

showNote :: Note -> String
showNote (Note _ d p) = showPitch p ++ show d

parseNote :: Voice -> String -> Note
parseNote v (s : o : d : [])     = Note v (digitToInt d) (Pitch (s : []) (o : []) "0")
parseNote v (s : a : o : d : []) = Note v (digitToInt d) (Pitch (s : []) (o : []) (a : []))

-- List of space-separated notes.
parseNotesV :: Voice -> String -> [Note]
parseNotesV v s = map (parseNote v) (words s)

parseNotes :: [String] -> [[Note]]
parseNotes xs = map (\(i,s) -> parseNotesV (show i) s) (zip [1..] xs)

measure :: Element -> Measure
measure e = Measure (attr "number" e) (map note (children "note" e))

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
part xs = childX "part" (onlyElems xs !! 1)

splitByVoice :: [Note] -> [[Note]]
splitByVoice = groupBy (\(Note v _ _) (Note w _ _) -> v == w)

-- Reorganize measures so that notes in each voice are put together.
-- Assumes voice ordering in each measure is the same.
reorg :: [Measure] -> [[Note]]
reorg ms = map concat (transpose (map (splitByVoice . mNotes) ms))

-- Reorganize list of voices of notes into measures.
deorg :: Int -> [[Note]] -> [Measure]
deorg notesPerMeasure nss =
  let xss = map (chunksOf notesPerMeasure) nss
      yss = map concat (transpose xss)
  in map (\(mn,ns) -> Measure (show mn) ns) (zip [1..] yss)

showMeasures :: [Measure] -> String
showMeasures ms = intercalate "\n" (map (\ns -> intercalate " " (map showNote ns)) (reorg ms))

xmlToMeasures :: String -> [Measure]
xmlToMeasures = measures . part . parseXML

xmeasure :: Measure -> Element
xmeasure (Measure mn notes) = unode "measure"
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
  "C58 E58 G58 F58 E58 C58 A58 F58 G58 E58 D58 C58" :
  "G48 C58 B48 A48 C58 A48 F48 A48 E58 G48 G48 G48" :
  "E48 E48 E48 F48 G38 C48 A38 F48 E48 E48 B38 C48" : []

test1 = parseNotes test
test2 = deorg 2 test1
test3 = measuresToXml test2

test4 = ppScore test3
test5 = xmlToMeasures test4
test6 = showMeasures test5
