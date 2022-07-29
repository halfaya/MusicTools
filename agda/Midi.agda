{-# OPTIONS --erased-cubical #-}

module Midi where

open import Agda.Builtin.String using (String)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)

open import MidiEvent using (Tick; MidiEvent; midiEvent; MidiTrack; track)

{-# FOREIGN GHC
  import System.Environment (getArgs)
  import Codec.Midi
  import Data.Text (Text, unpack, pack)
  import Data.List (sort, map)
  import Text.Read (readMaybe)

  type HsTicksPerBeat = Integer
  type HsTicks        = Integer
  type HsKey          = Integer
  type HsVelocity     = Integer
  type HsPreset       = Integer
  type HsChannel      = Integer
  type HsTempo        = Integer

  type HsAbsTime      = Integer

  type HsTrackName    = Text

  -- convert beats per minute to microseconds per beat
  bpmToTempo :: Int -> Tempo
  bpmToTempo bpm = round $ 1000000 * 60 / fromIntegral bpm

  data HsMidiMessage = HsNoteOn HsVelocity HsTicks HsKey | HsNoteOff HsVelocity HsTicks HsKey
    deriving Eq

  getTicks :: HsMidiMessage -> HsTicks
  getTicks (HsNoteOn  _ t _) = t
  getTicks (HsNoteOff _ t _) = t

  instance Ord HsMidiMessage where
    a <= b = getTicks a <= getTicks b

  data HsMidiTrack = HsMidiTrack HsTrackName HsPreset HsChannel HsTempo [HsMidiMessage]

  fi = fromInteger

  makeTrack :: Channel -> HsAbsTime -> [HsMidiMessage] -> (Track Ticks , HsAbsTime)
  makeTrack c t []                      = ([(0, TrackEnd)], t)
  makeTrack c t (HsNoteOn  v t' k : ms) = let (rest, t'') = makeTrack c t' ms
                                          in ((fi (t' - t), NoteOn  c (fi k) (fi v)) : rest, t'')
  makeTrack c t (HsNoteOff v t' k : ms) = let (rest, t'') = makeTrack c t' ms
                                          in ((fi (t' - t), NoteOff c (fi k) (fi v)) : rest, t'')

  toTrack :: HsMidiTrack -> Track Ticks
  toTrack (HsMidiTrack name preset channel tempo messages) =
    (0, TrackName (unpack name)) :
    (0, ProgramChange (fi channel) (fi preset)) :
    (0, TempoChange (bpmToTempo (fi tempo))) :
    fst (makeTrack (fi channel) 0 (sort messages))

  toMidi :: HsTicksPerBeat -> [HsMidiTrack] -> Midi
  toMidi ticks tracks = let mtracks = map toTrack tracks
                        in Midi MultiTrack (TicksPerBeat (fi ticks)) mtracks

  exportTracks :: Text -> HsTicksPerBeat -> [HsMidiTrack] -> IO ()
  exportTracks filePath ticksPerBeat tracks = do
    let path = unpack filePath
    putStrLn $ "Writing file " ++ path
    --putStrLn $ show $ toMidi ticksPerBeat tracks
    exportFile path (toMidi ticksPerBeat tracks)

  -- Returns n+1 if s parses as natural number n, or 0 for any failure
  readNat :: Text -> Integer
  readNat s = case (readMaybe (unpack s) :: Maybe Integer) of
    Just n  -> if n >= 0 then n+1 else 0
    Nothing -> 0
#-}

postulate
  IO       : Set → Set
  putStrLn : String -> IO ⊤
  getArgs  : IO (List String)
  _>>=_    : {A B : Set} -> IO A -> (A -> IO B) -> IO B  

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

{-# COMPILE GHC putStrLn = putStrLn . unpack #-}
{-# COMPILE GHC getArgs = fmap (fmap pack) getArgs #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b #-}

FilePath = String

data Pair (A : Set) (B : Set) : Set where
  pair : A → B → Pair A B

{-# COMPILE GHC Pair = data (,) ((,)) #-}

HInstrument HPitch HVelocity : Set
HInstrument = ℕ
HPitch      = ℕ
HVelocity   = ℕ
HChannel    = ℕ
HTempo      = ℕ

data MidiMessage : Set where
  noteOn  : HVelocity → Tick → HPitch → MidiMessage
  noteOff : HVelocity → Tick → HPitch → MidiMessage

{-# COMPILE GHC MidiMessage = data HsMidiMessage (HsNoteOn | HsNoteOff) #-}

event→messages : MidiEvent → List MidiMessage
event→messages (midiEvent p start stop v) =
  let v' = toℕ v
  in noteOn v' start p ∷ noteOff v' stop p ∷ [] 

data HMidiTrack : Set where
  htrack : String → HInstrument → HChannel → HTempo → List MidiMessage → HMidiTrack

{-# COMPILE GHC HMidiTrack = data HsMidiTrack (HsMidiTrack) #-}

track→htrack : MidiTrack → HMidiTrack
track→htrack (track n i c t m) = htrack n (toℕ i) (toℕ c) t (concatMap event→messages m)

postulate 
  exportTracks : FilePath        → -- path to the file to save the MIDI data to
                 ℕ               → -- number of ticks per beat (by default a beat is a quarter note)
                 List HMidiTrack → -- tracks, one per instrument
                 IO ⊤

{-# COMPILE GHC exportTracks = exportTracks #-}

postulate 
  readNat : String → ℕ

{-# COMPILE GHC readNat = readNat #-}
