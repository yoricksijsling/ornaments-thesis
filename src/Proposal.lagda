\begin{code}
module Proposal where
\end{code}

%<*example1>
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
%</example1>

%<*example2>
\begin{code}
_+_ : ℕ → ℕ → ℕ
\end{code}
%</example2>

\begin{code}
zero + y = y
suc x + y = suc (x + y)
\end{code}

