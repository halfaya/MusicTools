This supplementary material provides our implementation of
counterpoint (Counterpoint.agda) and harmony (Harmony.agda).

To compile and run the main program, do the following in this directory:

* `agda -c Main.agda`
* `./Main`

Note that you will need to modify `Main.agda` as it hardcodes some
local information.  Also you will need to run `cabal install HCodecs` for
the MIDI libraries if not already installed.  We are using Agda 2.6.1
(development) and GHC 8.6.5 but it probably works with other versions
as well.
