# MusicTools

To compile and run the main program, do the following in the `agda` directory.
Note that you will need to modify `Main.agda` as it hardcodes some local information.
Also you will need to `cabal install HCodecs` for the MIDI libraries if not already installed.
I am using Agda 2.6.1 (development) and GHC 8.6.5 but it probably works with other versions as well.
* `agda -c Main.agda`
* `./Main`

To make slides from source, Agda, XeLaTeX and the XITS font must be installed.
* In the agda directory, run `agda --latex Pnwplse.lagda`.
* Then in the slides directory, run `xelatex pnwplse.tex`.
This may need to be run more than once, for example if the number of pages changes.

Note that `\setsansfont` must be added to the default agda.sty file if the file is updated from the latest Agda distribution.
