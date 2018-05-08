module Midi where

open import Agda.Builtin.String using (String)
open import Data.Integer
open import Data.List
open import Data.Product using (_,_)

open import Note
open import Music

{-# FOREIGN GHC
  import Codec.Midi
  import Data.Text (Text)

  type HsChannel    = Integer
  type HsDuration   = Integer
  type HsNote       = Integer
  type HsTimedNote  = (HsNote, HsDuration)

  data HsMusic = HsMusicNote HsNote | HsMusicSeq HsMusic HsMusic | HsMusicPar HsMusic HsMusic

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

  toMidi :: HsChannel -> Integer -> HsMusic -> Midi
  toMidi c ticks es = let track = foldr (addMessage c) [(0, TrackEnd)] es
                      in Midi SingleTrack (TicksPerBeat (fi ticks)) [track]

  exportSong :: Text -> HsChannel -> Integer -> HsMusic -> IO ()
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

Channel     = ℤ

HDuration   = ℤ
HNote       = ℤ
HTimedNote  = Pair HNote HDuration

postulate 
  exportSong : FilePath →         -- path to the file to save the MIDI data to
               Channel →          -- MIDI channel that all data will be played on
               ℤ →                -- number of ticks per beat (by default a beat is a quarter note)
               List HTimedChord → -- sequence of timed chords to play
               IO Unit

{-# COMPILE GHC exportSong = exportSong #-}

-- Midi note value of middle C
middleC : ℤ
middleC = + 60

toHTimedChord : TimedChord → HTimedChord
toHTimedChord (chord ns , duration d) = pair (map (λ {(note n) → n}) ns) d

toHTimedChords : List TimedChord → List HTimedChord
toHTimedChords = map toHTimedChord
