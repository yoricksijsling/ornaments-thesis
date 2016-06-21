%include thesis.fmt

\chapter{A practical implementation of ornaments}


\section{Types in FP}

\subsection{Datatypes}

\begin{code}
data Bool : Set where
  false : Bool
  true : Bool

data Bool = false | true

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

take : ∀{A} → (n : Nat) → List A → List A
take zero    _        = []
take (suc n) []       = ?1
take (suc n) (x ∷ xs) = x ∷ take n xs

Maybe (List A)
nothing
\end{code}


\subsection{Inductive families}

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

takeᵥ : ∀{A m} → (n : Nat) →
  Vec A (n + m) → Vec A n
takeᵥ zero _ = []
takeᵥ (suc n) (x ∷ xs) = x ∷ takeᵥ n xs

smallest : List Nat → Maybe Nat
smallest [] = nothing
smallest (x ∷ xs) with smallest xs
smallest (x ∷ _) | nothing = just x
smallest (x ∷ _) | just m =
  just (if (lessNat x m) then x else m)

smallestᵥ : ∀{n} → Vec Nat n → Maybe Nat
smallestᵥ [] = nothing
smallestᵥ (x ∷ xs) with smallestᵥ xs
smallestᵥ (x ∷ _) | nothing = just x
smallestᵥ (x ∷ _) | just m =
  just (if (lessNat x m) then x else m)

\end{code}


\section{Descriptions}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

natDesc : DatDesc 2
natDesc = ι
  ⊕ rec-⊗ ι
  ⊕ `0

  nat-to : Nat → μ natDesc
  nat-to zero = ⟨ 0 , tt ⟩
  nat-to (suc n) = ⟨ 1 , nat-to n , tt ⟩
\end{code}

\begin{code}
--5 constructors:
  ι
  S ⊗ xs
  rec-⊗ xs
  `0
  x ⊕ xs

data StringList : Set where
  [] : StringList
  _∷_ : String → StringList → StringList

stringListDesc : DatDesc 2
stringListDesc = ι
  ⊕ (λ _ → String) ⊗ rec-⊗ ι
  ⊕ `0

ι
-⊗ xs⁺
rec-⊗ xs⁺
S +⊗ xs⁺
rec-+⊗ xs⁺
give-K
`0
x⁺ ⊕ xs⁺

nat→stringlist : DatOrn natDesc
nat→stringlist = ι
  ⊕ (λ _ → String) +⊗ rec-⊗ ι
  ⊕ `0

ornToDesc nat→stringlist ≡ stringListDesc

\end{code}

Dependent types

\begin{code}
IsLessThan7 : Nat → Set
IsLessThan7 n = n < 7

data Lt7 : Set where
  lt7 : (n : Nat) → IsLessThan7 n → Lt7

top γ
top (pop γ)
top (pop (pop γ))

lt7Desc : DatDesc 1
lt7Desc = (λ _ → Nat) ⊗
  (λ γ → IsLessThan7 (top γ)) ⊗ ι
  ⊕ `0

\end{code}