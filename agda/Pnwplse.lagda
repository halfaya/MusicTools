\begin{code}
open import Data.Integer
open import Data.Nat
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
