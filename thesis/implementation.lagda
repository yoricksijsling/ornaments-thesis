%include thesis.fmt

\chapter{Implementation}\label{sec:implementation}

\input{reflection.tex}

\section{Reflection of contexts}

|typeToCx|, |cxToTel|, |cxToType|

\section{Unquoting descriptions to datatypes}

Goal is to define two macros:

\begin{code}
unquoteDat : ∀{I Γ #c} (D : DatDesc I Γ #c) → Tactic
unquoteCon : ∀{I Γ #c} (D : DatDesc I Γ #c) (k : Fin #c) (`self : Term) → Tactic
\end{code}

\begin{code}
IType : (I : Cx₀) → TC Type
IType I = cxToType set₀ I >>= normalise

conDescTypeBare : ∀{I Γ} (`dt : Type) → ConDesc I Γ → TC Type
conDescTypeBare D =
  do `tel ← cxToTel Γ
  -| inContext `tel (helper 0 (cxVal 0 Γ) D >>= normalise)
\end{code}

\begin{code}
macro
  unquoteDat : ∀{I Γ #c} (D : DatDesc I Γ #c) → Tactic
  unquoteDat = giveTC (IType I)

  unquoteCon : ∀{I Γ #c} (D : DatDesc I Γ #c) (k : Fin #c) (`self : Term) → Tactic
  unquoteCon k `self = giveTC (conDescTypeBare `self (lookupCtor D k))
\end{code}


\section{Quoting of datatypes}

The goal is to create a |QuotedDesc|.


\begin{code}
parseConstructor : (`dt : Name) (#p : Nat) → ∀ I Γ → (offset : Nat) (ctel : AbsTelescope) (ctarget : Type) → TC (ConDesc I Γ)
\end{code}

\begin{code}
quoteConstructor : (`dt : Name) (#p : Nat) → ∀ I Γ → (`c : Name) → TC (ConDesc I Γ)
\end{code}

\begin{code}
quoteConstructors : (`dt : Name) (#p : Nat) → ∀ I Γ → (cnames : List Name) →
                    TC (DatDesc I Γ (length cnames))
quoteConstructors `dt #p I Γ [] = return `0
quoteConstructors `dt #p I Γ (cname ∷ cnames) =
  do c ← quoteConstructor `dt #p I Γ cname
  -| cs ← quoteConstructors `dt #p I Γ cnames
  -| return (c ⊕ cs)
\end{code}

\begin{code}
quoteDatatype : (`dt : Name) → TC QuotedDesc
quoteDatatype `dt =
  do dttype ← getType `dt
  =| #p ← getParameters `dt
  =| I ← typeToCx #p nothing dttype
  =| Γ ← typeToCx 0 (just #p) dttype
  =| `cnames ← getConstructors `dt
  =| datdesc ← quoteConstructors `dt #p I Γ `cnames
  =| return (mk `dt (listToVec `cnames) datdesc)
\end{code}

\section{Deriving HasDesc instances}

Stuff about α and β, from proposal.



\section{Discussion}
