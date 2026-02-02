import Xml

#eval Lean.versionString

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

partial def readString (stream : IO.FS.Stream) : IO String := do
  let s ← stream.getLine
  if s.isEmpty then pure ""
  else (s ++ ·) <$> readString stream

-- Lean XML parser has bug in parsing !DOCTYPE
-- https://github.com/leanprover/lean4/issues/12109
def discardHeader (stream : IO.FS.Stream) : IO IO.FS.Stream :=  do
  let _ ← stream.getLine -- ?xml
  let _ ← stream.getLine -- !DOCTYPE
  pure stream

def filePath := "/Users/leo/Downloads/Test.xml"

def mymain : IO String := do
  let stream ← fileStream filePath
  match stream with
    | none => pure ""
    | some s => discardHeader s >>= readString

#eval (List.map measures ∘ children "part" ∘ parseXml) <$> mymain
