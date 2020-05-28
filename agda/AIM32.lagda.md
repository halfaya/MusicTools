```agda
module AIM32 where

open import Pitch
open import Note
open import Music
```

# Music Tools Demo, AIM 32

Joint work with Youyou Cong

* Music Tools is a toolkit for exploring music using functional programming.
  Intended as a dependently-typed replacement for Euterpea.
  Goal is to have small, well-defined primitives that can be easily combined.

* Show Github repo, FARM and ICFP submissions.

* Demo of Hanon exercise.

* Music is an excellent domain for exploration of programming.
  Limited but still very rich.
  Most practical issues arise.
  Efficiency is not a big concern at present, so can concentrate on simplicity and elegance.
  Equivalences are especially prevalant, so a good candidate for Cubical.
  What are best practices for programming with dependent types?

* Current emphasis is on analysis and synthesis of Western common-practice music.
  A number of papers by Bas de Haas et al in Haskell have also explored this.
  Euterpea is more aimed as free-form creation of music using functional tools.

* One goal is to formalize music theory. Show texts.

* First and second species counterpoint.

* Harmonizaton of melodies.

* Coming up:
** More formalization of music theory.
** Integration with Cubical and exploration of equivalences, as well as ornaments.
** Exploration of tradeoffs: indexed types vs records, functions vs relations, 
