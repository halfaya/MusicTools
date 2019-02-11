{-# OPTIONS --without-K #-}

module Midi where

open import Agda.Builtin.String using (String)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ)
open import Data.List
open import Data.Product using (_,_)

open import Note
open import Pitch
open import MidiEvent
open import Music

{-# FOREIGN GHC
  import Codec.Midi
  import Data.Text (Text, unpack)
  import Data.List (sort)

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
    putStrLn "exportTracks"
    -- putStrLn $ show $ toMidi ticksPerBeat tracks
    exportFile (unpack filePath) (toMidi ticksPerBeat tracks)
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
      p' = getPitchValue p
  in noteOn v' start p' ∷ noteOff v' stop p' ∷ [] 

data HMidiTrack : Set where
  htrack : String → HInstrument → HChannel → HTempo → List MidiMessage → HMidiTrack

{-# COMPILE GHC HMidiTrack = data HsMidiTrack (HsMidiTrack) #-}

track→htrack : MidiTrack → HMidiTrack
track→htrack (track n i c t m) = htrack n (toℕ i) (toℕ c) t (concatMap event→messages m)

postulate 
  exportTracks : FilePath        → -- path to the file to save the MIDI data to
                 ℕ               → -- number of ticks per beat (by default a beat is a quarter note)
                 List HMidiTrack → -- tracks, one per instrument
                 IO Unit

{-# COMPILE GHC exportTracks = exportTracks #-}
