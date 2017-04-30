module Main where

import Scale
import Event
import Midi
import Codec.Midi

main :: IO ()
main = do
  let d = defaultTicksPerBeat
  let f x = (Note x, d)
  let cscale = map (+60) (diatonicScale ++ [12])
  let qscale = map f cscale ++ ((Silence, d) : map f (reverse cscale))
  let midi   = toMidi 0 qscale
  putStrLn $ show midi
  exportFile "test.mid" midi
