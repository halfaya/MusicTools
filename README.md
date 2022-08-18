# MusicTools

To compile and run the main program, do the following in the `agda` directory.
Note that you will need to modify `Main.agda` as it hardcodes some local information.
Also you will need to `cabal install --lib` the following libraries:
* `HCodecs`
* `sbv`

To use synthesis features, [Z3](https://github.com/Z3Prover/z3) must also be installed and in the path.

I am using the latest development versions of Agda/Agda-Stdlib/Cubical and GHC 9.2.2 but it may work with other versions as well.
No support is provided if it doesn't work.
* `agda -c Main.agda`
* `./Main`

To make slides from source, Agda, XeLaTeX and the XITS font must be installed.
* In the agda directory, run `agda --latex Pnwplse.lagda`.
* Then in the slides directory, run `xelatex pnwplse.tex`.
This may need to be run more than once, for example if the number of pages changes.

Note that `\setsansfont` must be added to the default agda.sty file if the file is updated from the latest Agda distribution.
