%include thesis.fmt

\chapter{A practical implementation of ornaments}


\section{Intro}

\subsection{Datatypes}

\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data List a = Nil | Cons a (List a)

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

find : List Nat →
  (P : Nat → Bool) → Maybe Nat
find [] P = nothing
find (x ∷ xs) P = if (P x) then (just x) else (find xs P)

findᵥ : ∀{n} → Vec Nat n →
  (P : Nat → Bool) → Maybe Nat
findᵥ [] P = nothing
findᵥ (x ∷ xs) P = if (P x) then (just x) else (findᵥ xs P)

find_b : ∀{mx} → BoundedNatList mx →
  (P : Nat → Bool) → Maybe Nat
find_b [] P = nothing
find_b (x ∷ xs) P = if (P x) then (just x) else (find_b xs P)

find_s : ∀{l} → SortedNatList l →
  (P : Nat → Bool) → Maybe Nat
find_s [] P = nothing
find_s (x ∷ xs) P = if (P x) then (just x) else (find_s xs P)

\end{code}


\subsection{Ornaments}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat
\end{code}


\section{Descriptions}

\begin{code}
data Desc : Set where
  `1 : Desc
  _⊕_ : Desc → Desc → Desc
  _⊗_ : Desc → Desc → Desc

⟦_⟧desc : Desc → Set
⟦ `1 ⟧desc = ⊤
⟦ A ⊕ B ⟧desc = Either ⟦ A ⟧desc ⟦ B ⟧desc
⟦ A ⊗ B ⟧desc = ⟦ A ⟧desc × ⟦ B ⟧desc

boolDesc : Desc
boolDesc = `1 ⊕ `1

⟦ `1 ⊕ `1 ⟧desc
  ≡ Either ⟦ `1 ⟧desc ⟦ `1 ⟧desc
  ≡ Either ⊤ ⊤

bool-to : Bool → ⟦ `1 ⊕ `1 ⟧desc
bool-to false = left tt
bool-to true = right tt

bool-from : ⟦ `1 ⊕ `1 ⟧desc → Bool
bool-from (left tt) = false
bool-from (right tt) = true
\end{code}

\begin{code}
pairOfBoolsDesc : Desc
pairOfBoolsDesc = (`1 ⊕ `1) ⊗ (`1 ⊕ `1)

pairOfBools : Set
pairOfBools = Bool × Bool
\end{code}


\section{Results (usage)}

\subsection{nats}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

unquoteDecl quotedNat NatHasDesc =
  deriveHasDesc quotedNat NatHasDesc (quote Nat)

quotedNat : QuotedDesc
NatHasDesc : HasDesc Nat

natDesc : Desc ε ε _
natDesc = QuotedDesc.desc quotedNat

natTo : Nat → μ natDesc tt tt
natTo = to

natFrom : μ natDesc tt tt → Nat
natFrom = from
\end{code}

\subsection{lists}

\begin{code}
data List (A : Set) : Set where
  nil : List A
  cons : (x : A) → (xs : List A) → List A

quotedList : QuotedDesc
ListHasDesc : ∀{A} → HasDesc (List A)

listDesc : Desc ε (ε ▷₁′ Set) _
listDesc = QuotedDesc.desc quotedList

listTo : ∀{A} → List A → μ listDesc (tt , A) tt
listTo = to

listFrom : ∀{A} → μ listDesc (tt , A) tt → List A
listFrom = from

gdepth : ∀{A} → ⦃ R : HasDesc A ⦄ → A → Nat
gdepth = gfold (depthAlg listDesc)

length : ∀{A} → List A → Nat
length = gdepth
\end{code}

\subsection{Ornaments}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

nat→list : Orn _ _ _ _ natDesc
nat→list = renameArguments 1 (just "xs" ∷ [])
  >>⁺ addParameterArg 1 "x"

test-nat→list : ornToDesc nat→list ≡ listDesc
test-nat→list = refl

list→vec : Orn _ _ _ _ listDesc
list→vec = algOrn (depthAlg listDesc)

vecDesc : Desc (ε ▷′ Nat) (ε ▷₁′ Set) _
vecDesc = ornToDesc list→vec
\end{code}


\section{Bonus}

% \begin{code}
% natDesc : DatDesc 2
% natDesc = ι
%   ⊕ rec-⊗ ι
%   ⊕ `0

%   nat-to : Nat → μ natDesc
%   nat-to zero = ⟨ 0 , tt ⟩
%   nat-to (suc n) = ⟨ 1 , nat-to n , tt ⟩
% \end{code}

\begin{code}
ι I
nm / S ⊗ xs
nm /rec I ⊗ xs
`0
x ⊕ xs

natDesc : DatDesc ε ε _
natDesc = ι (λ γ → tt)
  ⊕ "n" /rec (λ γ → tt) ⊗ ι (λ γ → tt)
  ⊕ `0

listDesc : DatDesc ε (ε ▷₁′ Set) _
listDesc = ι (λ γ → tt)
  ⊕ "x" / (λ γ → top γ)
  ⊗ "xs" /rec (λ γ → tt)
  ⊗ ι (λ γ → tt)
  ⊕ `0

vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) _
vecDesc = ι (λ γ → (tt , 0))
  ⊕ "n" / (λ γ → Nat)
  ⊗ "x" / (λ γ → top (pop γ))
  ⊗ "xs" /rec (λ γ → tt , top (pop γ))
  ⊗ ι (λ γ → tt , suc (top (pop γ)))
  ⊕ `0


ι J
nm /-⊗ xs⁺
nm /rec J ⊗ xs⁺
nm / S +⊗ xs⁺
nm /rec J +⊗ xs⁺
give-K
`0
x⁺ ⊕ xs⁺

\end{code}
