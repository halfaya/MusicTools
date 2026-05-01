/-import Lean.Data.Xml

namespace Xml

open Lean.Xml

def parseXml (s : String) : Element :=
  match parse s with
    | Except.error err =>
        Element.Element err Std.TreeMap.empty Array.empty
    | Except.ok e => e

abbrev Duration := Int
abbrev Step     := String
abbrev Octave   := String
abbrev Alter    := String
abbrev Voice    := String
abbrev MNum     := String

structure Pitch where
  pStep   : Step
  pAlter  : Alter
  pOctave : Octave
deriving Repr

structure Note where
  nVoice    : Voice
  nDuration : Duration
  nPitch    : Pitch
deriving Repr

structure Measure where
  mNum   : MNum
  mNotes : List Note
deriving Repr

def filterContent : String → Content → List Element
| s, Content.Element e@⟨n, _, _⟩ => if s == n then [e] else []
| _, _                           => []

def children : String → Element → List Element
| s, ⟨_, _, c⟩  => List.flatten (List.map (filterContent s) c.toList)

def child (s :String) (e : Element) : Element :=
  match children s e with
  | (c :: _) => c
  | []       => ⟨ "null", Std.TreeMap.empty, Array.empty ⟩

def attr : String → Element → String
| s, ⟨_, a, _⟩ => Std.TreeMap.getD a s "NOTFOUND"

-- child as a string
def cstr (s : String) (e : Element) : String :=
  match child s e with
  | ⟨_, _, c⟩  => c.map toString |>.foldl (· ++ ·) ""

def pitch (e : Element) : Pitch :=
  ⟨ cstr "step" e, cstr "alter" e, cstr "octave" e ⟩

def note (e : Element) : Note :=
  ⟨ cstr "voice" e,
    match String.toInt? (cstr "duration" e) with
    |  some i => i
    |  none   => -1,
    pitch (child "pitch" e) ⟩

def measure (e : Element) : Measure :=
  ⟨ attr "number" e, List.map note (children "note" e) ⟩

def measures (e : Element) : List Measure :=
  List.map measure (children "measure" e)


def abc : Pitch := ⟨ "a", "b", "c" ⟩

#eval abc

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
parseNote v (s : a : o : d) = Note v (read d) (parsePitch (s : a : o : []))

-- List of space-separated notes.
parseNotesV :: Voice -> String -> [Note]
parseNotesV v s = map (parseNote v) (words s)

parseNotes :: [String] -> [[Note]]
parseNotes xs = map (\(i,s) -> parseNotesV (show i) s) (zip [1..] xs)

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
  \<!DOCTYPE score-partwise PUBLIC '//Recordare//DTD MusicXML 3.1 Partwise//EN' 'http://www.musicxml.org/dtds/partwise.dtd'>\n"

ppScore :: Element -> String
ppScore e = header ++ ppElement e

-/
