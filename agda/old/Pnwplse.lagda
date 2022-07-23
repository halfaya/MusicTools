\begin{code}
{-# OPTIONS --without-K #-}

open import Data.Fin
open import Data.Integer
open import Data.Nat
open import Data.Product
\end{code}

%<*pitch>
\begin{code}
data Pitch : Set where
  pitch : ℤ → Pitch
\end{code}
%</pitch>

%<*duration>
\begin{code}
data Duration : Set where
  duration : ℕ → Duration
\end{code}
%</duration>

%<*note>
\begin{code}
data Note : Set where
  note : Duration → Pitch → Note
  rest : Duration         → Note
\end{code}
%</note>

%<*music>
\begin{code}
data Music : Set where
  note : Note → Music
  _∷_  : Music → Music → Music -- sequential
  _∥_  : Music → Music → Music -- parallel
\end{code}
%</music>

%<*chromatic>
\begin{code}
chromaticScaleSize : ℕ
chromaticScaleSize = 12
\end{code}
%</chromatic>

%<*relpitch>
\begin{code}
data RelativePitch : Set where
  relativePitch : Fin chromaticScaleSize → RelativePitch
\end{code}
%</relpitch>

%<*octave>
\begin{code}
data Octave : Set where
  octave : ℤ → Octave
\end{code}
%</octave>

%<*pitchoctave>
\begin{code}
PitchOctave : Set
PitchOctave = RelativePitch × Octave
\end{code}
%</pitchoctave>
