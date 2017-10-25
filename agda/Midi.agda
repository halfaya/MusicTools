module Midi where

open import Agda.Builtin.String using (String)
open import Data.Integer
open import Data.List
open import Data.Product using (_,_)

open import Note
open import Chord
open import TimedChord

{-# FOREIGN GHC
  import Codec.Midi
  import Data.Text (Text)

  type HsChannel    = Integer
  type HsDuration   = Integer
  type HsNote       = Integer
  type HsChord      = [HsNote]
  type HsTimedChord = (HsChord, HsDuration)

  defaultVelocity :: Velocity
  defaultVelocity = 60

  fi = fromInteger

  addMessage :: HsChannel -> HsTimedChord -> Track Ticks -> Track Ticks
  addMessage c ((ns@(n:ns')), d) ts
    = map (\n -> (0, NoteOn (fi c) (fi n) defaultVelocity)) ns ++
      [(fi d, NoteOff  (fi c) (fi n) defaultVelocity)] ++
      map (\n -> (0, NoteOff (fi c) (fi n) defaultVelocity)) ns' ++ ts
  addMessage c ([], d) ((t,m):ts) = (t + (fi d),m):ts
  addMessage c ([], _) []         = []

  toMidi :: HsChannel -> Integer -> [HsTimedChord] -> Midi
  toMidi c ticks es = let track = foldr (addMessage c) [(0, TrackEnd)] es
                      in Midi SingleTrack (TicksPerBeat (fi ticks)) [track]

  -- ticks is the number of ticks per beat (by default a beat is a quarter note)
  exportSong :: Text -> HsChannel -> Integer -> [HsTimedChord] -> IO ()
  exportSong filePath channel ticksPerBeat song =
    exportFile (Data.Text.unpack filePath) (toMidi channel ticksPerBeat song)
#-}

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

FilePath = String

data Pair (A : Set) (B : Set) : Set where
  pair : A → B → Pair A B

{-# COMPILE GHC Pair = data (,) ((,)) #-}

HDuration   = ℤ
HChannel    = ℤ
HNote       = ℤ
HChord      = List HNote
HTimedChord = Pair HChord HDuration

postulate 
  exportSong : FilePath → HChannel → ℤ → List HTimedChord → IO Unit

{-# COMPILE GHC exportSong = exportSong #-}

-- Midi note value of middle C
middleC : ℤ
middleC = + 60

toHTimedChord : TimedChord → HTimedChord
toHTimedChord (chord ns , duration d) = pair (map (λ {(note n) → n}) ns) d

toHTimedChords : List TimedChord → List HTimedChord
toHTimedChords = map toHTimedChord
