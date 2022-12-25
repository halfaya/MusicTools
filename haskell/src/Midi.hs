{-# LANGUAGE ScopedTypeVariables #-}

module Midi where

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
