%include proposal.fmt

\section{Literature review}\label{sec:lit}

Ornaments are strongly related to generic programming.
In particular, many current implementations of ornaments work on
generic representation of datatypes \cite{dagand12,dagand14-essence,dagand14-transporting}.
We will give an overview of generic programming using dependent
types, starting with a universe of finite types in section
\ref{sec:lit-finite}.
Universes for context-free types with and without multiple fixed
points shown in section \ref{sec:lit-cft} and \ref{sec:lit-indexed}.
Section \ref{sec:lit-k} shows some ways in which references to other
types can be described.
For our work we will be using reflection, which is discussed in
section \ref{sec:lit-reflection}.
Finally we will describe ornaments in section
\ref{sec:lit-ornaments}.

% PAPERS

% \begin{enumerate}
%   \item A categorical treatment of ornaments \cite{dagand12}: no clue
%   \item Categorical organisation of the ornament-refinement
%     framework \cite{kogibbons13}: ...
%   \item Generic programming with dependent types \cite{altenkirch06}:
%     Universe descriptions of finite/cft/spt types.
%     Containers.
%     Derivatives of cft.
%   \item Generic programming with fixed points for mutually recursive
%     datatypes \cite{yakushev09}:
%   \item Inductive families need not store their indices \cite{brady04}
%   \item Modularising inductive families ...
%   \item Ornaments in practice \cite{williams14}:
%     Ornaments implemented in a subset of ML
%   \item The essence of ornaments \cite{dagand14-essence}:
%     Ornaments on signatures
%   \item The gentle art of levitation \cite{chapman10}:
%     Descriptions
%   \item Transporting functions across ornaments \cite{dagand14-transporting}:
%     Ornaments on descriptions with var, 1, Π and Σ.
%     Stuff like functional ornaments, ornamental algebra's, algebraic
%     ornaments, reornaments,
% \end{enumerate}

\subsection{Universe for finite types}\label{sec:lit-finite}

Finite types are all those types which have a finite number of
inhabitants.
If a type has $n$ inhabitants, these inhabitants correspond to those
of |Fin n|, where |Fin n| can represent all natural numbers up to
$n$.

A practical way of describing finite types is by defining them with a
generative grammar\cite{altenkirch06}:

\[
  τ = 0 \mid 1 \mid τ + τ \mid τ * τ
\]

$0$ and $1$ are for the empty and unit type respectively.
$*$ is used for products and $+$ for coproducts (sums).

This can be formalized with a universe construction\cite{martinloef84}
in Agda using the |Desc| datatype:

\begin{code}
data Desc : Set where
  `0 : Desc
  `1 : Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
\end{code}

We write an interpretation function which converts descriptions to a
type of which the inhabitants correspond uniquely to the inhabitants
of the described type.

\begin{code}
⟦_⟧ : Desc → Set
⟦ `0 ⟧ = ⊥
⟦ `1 ⟧ = ⊤
⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A `* B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
\end{code}

\begin{example}[Description of a pair of booleans]
As a finite type, a pair of two booleans can be expressed as
$\PairOfBools = (1 + 1) * (1 + 1)$.
The equivalent description in our universe is simply
|pairOfBoolsDesc = (`1 `+ `1) `* (`1 `+ `1)|.
Interpretation of that description, |⟦ pairOfBoolsDesc ⟧|,
results in the type |(⊤ ⊎ ⊤) × (⊤ ⊎ ⊤)|.
It is easy to verify that every inhabitant of this type corresponds
uniquely to an inhabitant of a pair of two booleans; they are
isomorphic.
\end{example}

A finite type in this universe might be in a strict sum-of-products
form: $(x * ⋯ * x) + ⋯ + (x * ⋯ * x)$, where all $x$es are $0$ or
$1$.
If this is the case, it can be directly interpreted as an algebraic
datatype.
The products correspond to constructors, and the factors of those
products correspond to constructor arguments.
If a finite type is not in sum-of-products form, for example
$\PairOfBools = (1 + 1) * (1 + 1)$, the correspondence is not so
obvious and we may need multiple datatypes to represent it.

\subsubsection{Types and their descriptions}

If we have some datatype in our host language which corresponds to
some description, we can relate the two by providing an
embedding-projection pair.

\begin{definition}[Embedding-projection pair for finite types]\label{def:ep-pair-finite}
  An \emph{embedding-projection pair} is a pair of functions
  translating between the interpretation of a description |⟦ D
    ⟧| and the corresponding datatype |X|.
  They have the types |to : X → ⟦ D ⟧| and |from : ⟦ D ⟧ → X|.
\end{definition}

To really prove that the datatype and the interpretation are
isomorphic, we also need to prove that |to| and |from| are inverses.
This is done with the following functions:

\begin{code}
to-from : ∀ x → from (to x) ≡ x
from-to : ∀ x → to (from x) ≡ x
\end{code}

Together |to|, |from|, |to-from| and |from-to| form an isomorphism
(more specifically a bijection).

\subsection{Universe for context-free types}\label{sec:lit-cft}

We can extend our grammar for finite types to context-free
types by adding a $μ$ operator to construct inductive types.
For instance, $\Nat$ can be expressed as $\Nat = μX. 1 + x$.
Type parameters are included as variable bindings with a $λ$.
So List might be written as $\List = λA. μX. 1 + A * X$ or simply
$\List A = μX. 1 + A * X$.
Context-free types also allow multiple variable bindings; rose trees
can be expressed as $\RoseTree A = μX. \List (A * X) = μX. μY. 1 + (A
* X) * Y$.
The grammar for context-free types is:

\[
  τ = α \mid 0 \mid 1 \mid τ + τ \mid τ * τ \mid μα. τ \mid λα. τ
\]

\subsubsection{Naively}

To represent these types we have to be able to bind variables.
Following Altenkirch et al \cite{altenkirch06}, we might expand the
definition of \AD{Desc} to represent these operations.
We introduce a \AD{ℕ} index to indicate the number of free variables.

% \InsertCode{contextfree-naive-desc}
\begin{code}
data Desc : ℕ → Set where
  `0 : ∀{n} → Desc n
  `1 : ∀{n} → Desc n
  _`+_ : ∀{n} → (A B : Desc n) → Desc n
  _`*_ : ∀{n} → (A B : Desc n) → Desc n
  `var : ∀{n} → Fin n → Desc n
  `mu : ∀{n} → Desc (suc n) → Desc n
\end{code}

Now we can describe all the context-free types.
However, an interpretation function |⟦_⟧| is not so
straightforward.
A naive definition of this function will not be accepted by Agda's
termination checker.
Indeed, when we try to interpret |natDesc = ‵1 ‵+ `var zero| we get an
expanding term |⟦ natDesc ⟧ =⊤ ⊎ ⟦ natDesc ⟧ = ⋯|

\subsubsection{Using functors}\label{sec:lit-cft-single}

A common solution to this non-termination is by interpreting a
description as a functor, and then taking the fix point.
With this method we get rid of the explicit |μ| constructor in the
description type, because we always assume an implicit $μ$ in front of
it.
The interpretation function |⟦_⟧| is now of type |Desc → Set → Set|,
so it takes a |Desc| and gives us a \emph{pattern functor} on |Set|.
Taking the fix point of the |Set|-endofunctor gives us a |Set|
we can use, a process known as \emph{tying the knot}.

% \InsertCode{contextfree-one-base}
\begin{code}
data Desc : Set where
  `0 : Desc
  `1 : Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
  `var : Desc

⟦_⟧ : Desc → Set → Set
⟦_⟧ `0 X = ⊥
⟦_⟧ `1 X = ⊤
⟦_⟧ (A `+ B) X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
⟦_⟧ (A `* B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦_⟧ `var X = X

data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D
\end{code}

Note that in general fixed points do not necessarily terminate, so they
do not pass Agda's termination checker.
Therefore we use a fix point construction specialised to
the interpretation function |⟦_⟧|.
The termination checker inspects the definition of |⟦_⟧| to see
that none of the clauses introduce unbounded recursion.

With the addition of |μ| we have to adjust our notion of
embedding-projection pairs (definition \ref{def:ep-pair-finite}).
\begin{definition}[Embedding-projection pair for context-free types]
  An \emph{embedding-projection pair} is a pair of functions
  translating between the interpretation of a description |μ D|
  and the corresponding datatype |X|.
  They have the types |X → μ D| and |μ D → X|.
\end{definition}

\begin{example}[Description of naturals]
The datatype for naturals requires recursion, and can now be
described in our universe with:

\begin{code}
natDesc = `1 `+ `var
\end{code}

To see how this description relates to the original datatype, we give
the embedding-projection pair:

\begin{code}
to : ℕ → μ natDesc
to zero = ⟨ inj₁ tt ⟩
to (suc n) = ⟨ inj₂ (to n , tt) ⟩

from : μ natDesc → ℕ
from ⟨ inj₁ tt ⟩ = zero
from ⟨ inj₂ (n , tt) ⟩ = suc (from n)
\end{code}
\end{example}

This formalization of context free types is limited in two ways:
\begin{itemize}
\item It allows only one fixed point. Therefore it can only describe types
with a single $μ$ variable binding.
\item |`var| always refers to the implicitly bound $μ$, so
  datatype parameters are not supported.
\end{itemize}

\subsection{Universe for indexed functors}\label{sec:lit-indexed}
\label{sec:lit-indexed}

In the previous section we described a universe where the
interpretation gives back a functor |Set → Set|.
In that case, the |Set| argument is used directly in the
interpretation of |`var|.
We have already seen how |`var| can be used to reference
multiple variables by passing in a |Fin n| in section
\ref{sec:lit-cft}, or more generally \emph{some} index which specifies
what variable to use.

\emph{Indexed descriptions} are parameterized over two sets, an input
type |I| and an output type |O|.

\begin{code}
data IODesc : Set → Set → Set₁ where
  `0 : ∀{I O} → IODesc I O
  `1 : ∀{I O} → IODesc I O
  _`+_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
  _`*_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
  `var : ∀{I O} → I → IODesc I O
\end{code}

An indexed description |IODesc I O| is interpreted as an
indexed functor |(I → Set) → (O → Set)|.
If both |I| and |O| are instantiated to |⊤| this is isomorphic to
a normal functor as in section \ref{sec:lit-cft-single}.

\begin{code}
IOFunc : Set → Set → Set₁
IOFunc I O = (I → Set) → (O → Set)

⟦_⟧ : ∀{I O} → IODesc I O → IOFunc I O
⟦_⟧ `0 r o = ⊥
⟦_⟧ `1 r o = ⊤
⟦_⟧ (A `+ B) r o = ⟦ A ⟧ r o ⊎ ⟦ B ⟧ r o
⟦_⟧ (A `* B) r o = ⟦ A ⟧ r o × ⟦ B ⟧ r o
⟦_⟧ (`var I) r o = r I
\end{code}

In the interpretation one can use a function |r : I → Set| which
returns a type given a \emph{request} of type |I|.
There is also a \emph{received} request |o| which is used as a
selector for which type we must respond with.
We use the term request rather vaguely on purpose because it is used
for different things; which we will explain in the following sections.
For a full implementation of this universe we refer the reader to
\cite{loeh11}.

\subsubsection{Parameters}\label{sec:lit-indexed-parameters}

The request to the function |r| can be used to refer to
parameters.

\begin{example}
One might describe a datatype for pairs as

\begin{code}
PairDesc : IODesc (⊤ ⊎ ⊤) ⊤
PairDesc = `var (inj₁ tt) `* `var (inj₂ tt)
\end{code}

In this case the datatype can make requests of type |⊤ ⊎ ⊤|,
while the request it \emph{receives} (|o|) is just a |⊤|.
We can build a response function which returns a type depending on the
value of the request:

\begin{code}
select : (A B : Set) → ⊤ ⊎ ⊤ → Set
select A B (inj₁ tt) = A
select A B (inj₂ tt) = B
\end{code}

By interpreting the type we see that for any |A| and |B|,
|⟦ PairDesc ⟧ (select A B) tt| evaluates to |A × B|.
\end{example}

\subsubsection{Recursion}

The |`var| constructor can also be used for recursive calls.
In that case the request of type |I| is passed to the datatype
itself as the |o| value, so the input type |I| must
correspond in some way with the output type |O|.
If the input and output indices are exactly the same, as in
|IOFunc O O|, the fixed point is of type |IOFunc ⊥ O|.
Recursive types may still have parameters, which we will keep outside
of the fixed point, so a functor with parameters of type |I|
and recursive calls of type |O| has the type |IOFunc (I + O) O|, which
has a fixed point of type |IOFunc I O|.

Notice that the indexed functors are closed under fixed points,
contrary to non-indexed functors of type |Set → Set| which have
a |Set| as their fixed point.
Consequently, we can implement |`Fix| as a constructor of
|IODesc|, allowing us to have multiple fixed points within a
datatype.

\begin{code}
`Fix : ∀{I O} → IODesc (I ⊎ O) O → IODesc I O
⟦_⟧ (`Fix F) r o = μ F r o
\end{code}

The interpretation of |`Fix| uses a new |μ| datatype
which represents a fixed point on the output indices |O| but it
does not touch the parameters |I|.
An implementation of |μ| is found in \cite{loeh11}.

\begin{example}
With parameters and recursion in place we can now describe Lists in
this universe.
Recall the representation of lists: $\List = λA. μX. 1 + A * X$.
The part under the $μ$ has two unbound variables and returns
one type.
This is represented with a description of type |IODesc (⊤ ⊎ ⊤) ⊤|.
By binding the $X$ with a fixed point a description of type
|IODesc ⊤ ⊤| is left:

\begin{code}
ListFDesc : IODesc (⊤ ⊎ ⊤) ⊤
ListFDesc = `1 `+ (`var (inj₁ tt) `* `var (inj₂ tt))

ListDesc : IODesc ⊤ ⊤
ListDesc = `Fix ListFDesc
\end{code}

Every list can be translated to a description:

\begin{code}
fromList : ∀{A} → List A → ⟦ ListDesc ⟧ (λ _ → A) tt
fromList [] = ⟨ inj₁ tt ⟩
fromList (x ∷ xs) = ⟨ inj₂ (x , fromList xs) ⟩
\end{code}
\end{example}


\subsubsection{Mutually recursive datatypes}

Indexed fixed points are suitable to express families of mutually
recursive datatypes \cite{yakushev09}.
The request is then used to select which datatype to use.

\begin{example}[Trees]
A simple mutually recursive family is the one for trees where each
node has an arbitrary number of subtrees:

\begin{code}
mutual
  data Tree (A : Set) : Set where
    empty : Tree A
    node : A → Forest A → Tree A
  data Forest (A : Set) : Set where
    nil : Forest A
    cons : Tree A → Forest A → Forest A
\end{code}

We introduce |WoodTag| to enumerate the two types.
Note that any type with exactly two inhabitants would work.

\begin{code}
data WoodTag : Set where
  tree forest : WoodTag
\end{code}

Within the descriptions of both types we can refer to the parameter
|A| and the datatypes |Tree| and |Forest|.
This is indicated with the type of the input index: |⊤ ⊎ WoodTag|.
The separate types can be described in the normal way:

\begin{code}
TreeDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
TreeDescF = `1
         `+ `var (inj₁ tt) `* `var (inj₂ forest)

ForestDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
ForestDescF = `1
           `+ `var (inj₂ tree) `* `var (inj₂ forest)
\end{code}

These descriptions now have to be combined in some way, where we use
the output index of type |WoodTag| to pick the right one.
\end{example}

We do not yet have any constructor of |IODesc| which uses the
output index of type |O|.
A simple solution is to introduce a constructor |`!|; it takes
a value of type |O|:

\begin{code}
`! : ∀{I O} → O → IODesc I O
\end{code}

It is interpreted as an equality matching the provided value with
the actual value of |o|, imposing a \emph{constraint} on the
datatype.

\begin{code}
⟦_⟧ (`! o′) r o = o ≡ o′
\end{code}

\begin{example}[Trees continued]\label{ex:trees2}
Using the |`!| constructor we can combine the descriptions of
|Tree| and |Forest|.
We basically add a constraint to each description, and then sum them
together.

\begin{code}
WoodDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
WoodDescF = `! tree `* TreeDescF
         `+ `! forest `* ForestDescF

WoodDesc : IODesc ⊤ WoodTag
WoodDesc = `Fix WoodDescF
\end{code}

The presence of the absurd patterns in the definitions of
|toTree| and |toForest| shows how the constraint can not
be solved when the wrong branch is picked:

\begin{code}
toTree : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) tree → Tree A
toTree ⟨ inj₁ (refl , inj₁ tt) ⟩ = empty
toTree ⟨ inj₁ (refl , inj₂ (x , f)) ⟩ = node x (toForest f)
toTree ⟨ inj₂ (() , _) ⟩
toForest : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) forest → Forest A
toForest ⟨ inj₁ (() , _) ⟩
toForest ⟨ inj₂ (refl , inj₁ tt) ⟩ = nil
toForest ⟨ inj₂ (refl , inj₂ (t , f)) ⟩ = cons (toTree t) (toForest f)
\end{code}
\end{example}

\subsubsection{Indices}

Representing inductive families is essentially the same problem as
representing mutually recursive families.
This is exemplified by the fact that we could have rewritten the mutually
recursive family of example \ref{ex:trees2} to an isomorphic inductive family:

\begin{code}
data Wood (A : Set) : WoodTag → Set where
  empty : Wood A tree
  node  : A → Wood A forest → Wood A tree
  nil   : Wood A forest
  cons  : Wood A tree → Wood A forest → Wood A forest
\end{code}

Given this definition it is not immediately obvious why the description 
would first split on the index as in example \ref{ex:trees2}.

To understand how inductive families are described in our
universe, it is instructive to use \emph{index-first} notation
\cite{ko11}.
The usual interpretation of Agda datatypes is that the index of the
result type is computed from the chosen constructor and its
arguments.
For example, if we choose to use the |empty| constructor of the
|Wood| datatype the index is going to be |tree|.
This perspective can be turned around:
We might say that \emph{if} we want to create a |Wood A tree|
\emph{then} we can only use the constructors |empty| and
|node|.
Index-first notation emphasizes this way of thinking.
The |Wood| datatype is written as follows:

\begin{code}
indexfirst data Wood (A : Set) : WoodTag → Set where
  Wood A tree   ∋ empty
                | node   (x : A) (f : Wood A forest)
  Wood A forest ∋ nil
                | cons   (t : Wood A tree) (f : Wood A forest)
\end{code}

By writing it this way, it becomes clear that we first have to
look at the required index, before determining what description to
use. The description of this indexed datatype is exactly the same as
that of the inductive family containing |Tree| and |Forest|.

\subsection{Referring to other types}\label{sec:lit-k}

Consider lists of naturals: $\NatList = μX. 1 + ℕ * X$.
Notice that we refer to another type $ℕ$ here.
Up to this point, our universes do not have a way to represent this
directly.
In the universe for indexed functors we could replace $ℕ$ by its
description giving us $\NatList = μX. 1 + (μY. 1 + Y) * X$; this
relies on the ability to represent nested fixed points.
If the universe does not allow nested fixed points we need another
way.

\subsubsection{Constants}\label{sec:lit-constants}

The classic way to do this is by introducing a |`K|
constructor.
Starting with the universe of section \ref{sec:lit-cft-single} we add
the following constructor:

\begin{code}
`K : (S : Set) → Desc
\end{code}

The interpretation of |`K| is the constant functor:

\begin{code}
⟦ `K S ⟧ X = S
\end{code}

Do note that this variant of |`K| only supports constants of
sort |Set₀|, and it forces |Desc| to be in |Set₁| (it was in |Set₀|).
It is not possible to make the constructor level-polymorphic, because
the level of the datatype would then depend on a constructor argument,
which is not allowed in Agda.

This constructor conveniently supports inclusion of arbitrary
user-defined datatypes, but it introduces problems too.
Most importantly, some functions such as decidable equality become
impossible to define because we do not know anything about the
included type \cite{loeh11}.
Ideally, one would like to refer to descriptions instead of |Set|s,
forcing the included type to be describable in our universe.
However, this would essentially allow us to describe types with
multiple fixed points which is not possible in this universe.

\subsubsection{Rewriting by isomorphism}

In universes where we do have multiple fixed points, something like
|`K| can be implemented differently, by actually referring to a
description.
It can be useful to clarify that the included description corresponds
to some agda datatype.
We can do this using the |`Iso| constructor \cite{loeh11},
which we define for the universe for indexed functors of section
\ref{sec:lit-indexed}:

\begin{code}
`Iso : ∀{I O} → (C : IODesc I O) → (D : IOFunc I O)
       ((r : I → Set) → (o : O) → D r o ≃ ⟦ C ⟧ r o) → IODesc I O
\end{code}

Here the |_≃_| can be read as 'is isomorphic to', so the
interpretation of the description and the given indexed functor are
isomorphic.
The interpretation uses the indexed functor to return a type.

\begin{code}
⟦_⟧ (`Iso C D) r o = D r o
\end{code}

\begin{example}
We can give the description of naturals:

\begin{code}
ℕDesc : IODesc ⊥ ⊤
ℕDesc = `Fix (`1 `+ `var (inj₂ tt))

ℕDescIso : IODesc ⊥ ⊤
ℕDescIso = `Iso ℕDesc (λ _ _ → ℕ) ℕDesc-iso
\end{code}

The interpretation of the type, |⟦ ℕDescIso ⟧ (λ ()) tt|, is
now |ℕ|.
It effectively hides what the description looks like and thereby
improves the reusability of the defined description.
\end{example}

\begin{remark}
This implementation of |`Iso| does not pass the strict-positivity
checker of Agda.
|⟦_⟧| occurs in an argument to the single constructor of |μ|, which
means that a reference to |μ| is only allowed in strictly positive
position in every clause of |⟦_⟧|, so a right hand side (RHS) |μ F r o| is
fine but an RHS |μ F r o → A| is not.
The RHS of the clause for |`Iso| is |D r o|, where |D : IOFunc I O|
and |r : I → Set|.
This could result in a term where |μ| is used in the wrong position.
\end{remark}

\subsubsection{Σ using Set}\label{sec:lit-sigmaset}

The description types we have seen all have sums and products using
$+$ and $*$.
In dependently typed languages we have |Σ|-types, which can be
interpreted as both sums and products \cite{chapman10}.

The type |Σ[ x ∈ A ] B x| can be seen as a product of
|A| and |B x|, which matches with the |_`*_|
constructor.
Alternatively, it can function as a sum of an arbitrary number of
types; a chain of |_`+_|es
In that case |x| is used to select a position, and the type on
that position is |B x|.

With this knowledge, we could have defined a universe with the same
functionality as the one in section \ref{sec:lit-cft-single} as such:

\begin{code}
data Desc : Set₁ where
  `1 : Desc
  `Σ : (S : Set) → (D : S → Desc) → Desc
  `var : Desc
\end{code}

Where |`Σ| is interpreted as a |Σ|-type:

\begin{code}
⟦_⟧ (`Σ S D) X = Σ S (λ s → ⟦ D s ⟧ X)
\end{code}

Interestingly, the |`Σ| also replaces |`K| and
|`0|:

\begin{code}
`K_`*_ : (S : Set) → Desc → Desc
`K S `* D = `Σ S (λ _ → D)

`0 : Desc
`0 = `Σ ⊥ ⊥-elim
\end{code}

\begin{example}
Now list of naturals can be defined as a sigma-of-sigmas:

\begin{code}
natlist : Desc
natlist = `Σ (⊤ ⊎ ⊤) (λ { (inj₁ tt) → `1
                        ; (inj₂ tt) → `K ℕ `* `var
                        })
\end{code}
\end{example}

\subsubsection{Σ using descriptions}

The |`Σ| defined in the previous section uses a |Set| as
the first argument.
This has the same drawbacks as using a |Set| for
|`K| (see section \ref{sec:lit-constants}).
This can be avoided by restricting the argument to descriptions.
We define the constructor in the indexed functor universe:

\begin{code}
`Σ : ∀{I O} → {C : IODesc ⊥ ⊤} →
     (f : ⟦ C ⟧ (λ _ → ⊤) tt → IODesc I O) → IODesc I O
\end{code}

The interpretation is a witness paired with some description which
depends on the value of the witness:

\begin{code}
⟦_⟧ (`Σ f) r o = ∃ (λ i → ⟦ f i ⟧ r o)
\end{code}

The witness is of type |⟦ C ⟧ (λ _ → ⊤) tt| and is passed straight to
a function which gives back a description.
For such cases |`Iso| can be very useful, because it allows us to pass
a more useful type to this function.
In the case of naturals the function would simply get a |ℕ|, instead
of something like |μ (`1 `+ `var (inj₂ tt)) (λ ()) tt|.

\subsection{Reflection}\label{sec:lit-reflection}

Agda supports quoting using a few built-in keywords and datatypes.
Datatypes and constructors of the types related have to be bound to an
identifier using |BUILTIN| pragma's.
This has been done in Agda's standard library (version 2.4.2.3), and
identifiers we will be using are taken from there.
We will give a high-level overview of the reflection mechanism.

\subsubsection{Quoting terms}

One of the datatypes related to quoting is |Term|, which reflects a
code fragment.
It has constructors for references to variables, constructors and
definitions, lambda-abstractions and pattern matching
lambda-abstractions, pi-types, sorts and literals.
Application is done by including a list of arguments where applicable.
Variables bound by lambda-abstractions do not have names; they are
referred to using their De Bruijn index.

\begin{code}
data Term : Set where
  var     : (x : ℕ) (args : List (Arg Term)) → Term
  con     : (c : Name) (args : List (Arg Term)) → Term
  def     : (f : Name) (args : List (Arg Term)) → Term
  lam     : (v : Visibility) (t : Term) → Term
  pat-lam : (cs : List Clause) (args : List (Arg Term)) → Term
  pi      : (t₁ : Arg Type) (t₂ : Type) → Term
  sort    : Sort → Term
  lit     : Literal → Term
  unknown : Term
\end{code}

Terms can be used as types, by pairing it with a |Sort| indicating in
which |Set| it lies.

\begin{code}
data Type : Set where
  el : (s : Sort) (t : Term) → Type
\end{code}

To use something as an argument, one has to provide some information
about the visibility and relevance of the argument.
We will skip the details and assume that there is a function |argᵥᵣ|:

\begin{code}
argᵥᵣ : ∀{A} → A → Arg A
\end{code}

A code fragment can be quoted to a |Term| using |quoteTerm|.
For instance:

\begin{code}
quoteTerm (λ (f : ℕ → Bool) → f 2)
 ≡ lam visible (var 0 (argᵥᵣ (lit (nat 2)) ∷ []))
\end{code}

The inverse operation of |quoteTerm| is |unquote|.
This takes an argument of type |Term| which is normalized and type
checked.
It is then treated as if the user had written the code there directly.

\subsubsection{Names}

To be able to use existing definitions, one has to have a |Name| for
it.
This is an internal type, and values of this type can be obtained by
using the |quote| keyword.
For example:

\begin{code}
unquote (def (quote ℕ) []) ≡ ℕ
\end{code}

It is important to note that the argument for |quote| can only be a
defined name, nothing else.
It can not be a variable or a term, so a construction like |λ x →
quote x| or even |quote ((λ x → x) ℕ)| is invalid.

Besides using it directly in a |Term|, one can retrieve the type and
definition of a given name:

\begin{code}
type         : Name → Type
definition   : Name → Definition
\end{code}

The |Definition| indicates what kind of definition it is, and might
have some additional information attached.
For constructors, axioms and primitives there is no more information;
one can already get the type with the |type| function.

\begin{code}
data Definition : Set where
  function     : FunctionDef  → Definition
  data-type    : Data-type → Definition
  record′      : Record    → Definition
  constructor′ : Definition
  axiom        : Definition
  primitive′   : Definition
\end{code}

If a definition is a datatype, we get a value of type |Data-type|.
This can be used to retrieve the names of the constructors, which can
then be used to get the types of those.

\begin{code}
constructors : Data-type → List Name
\end{code}

\subsubsection{Parameters and indices}

The reflected types of datatypes and constructors include any
parameters and indices.
However, given just the types one cannot discern between parameters
and indices.
The current version of Agda (2.4.2.3) has no other way to distinguish
between the two.

\begin{example}[Lists]
Take the following type for lists:

\begin{code}
data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A
\end{code}

To get the type of |ListP|, we can use |type (quote ListP)| which
returns a value of type |Type|.

\begin{code}
type (quote ListP) ≡ el _ (pi (argᵥᵣ (el _ (sort (lit 0)))) (el _ (sort _)))
\end{code}

These values are quite hard to read, but we can use |quoteTerm| on the
right hand side to make it easier.
All the following equalities hold:

\begin{code}
type (quote ListP)      ≡ el _ (quoteTerm ((A : Set) → Set))
type (quote ListP.[])  ≡ el _ (quoteTerm ({A : Set} → ListP A))
type (quote ListP._∷_) ≡ el _ (quoteTerm ({A : Set} → A → ListP A → ListP A))
\end{code}

Notice how the datatype parameter is explicit in the type of |ListP|,
and becomes implicit in the types of the constructors.
Now compare this with a variant of |ListP| which uses indices instead
of a parameter:

\begin{code}
data ListI : (A : Set) → Set₁ where
  [] : ∀{A} → ListI A
  _∷_ : ∀{A} → A → ListI A → ListI A

type (quote ListI)      ≡ el _ (quoteTerm ((A : Set) → Set₁))
type (quote ListI.[])  ≡ el _ (quoteTerm ({A : Set} → ListI A))
type (quote ListI._∷_) ≡ el _ (quoteTerm ({A : Set} → A → ListI A → ListI A))
\end{code}

Apart from the necessary change of the sort from |Set| to |Set₁|, the
reflected types are exactly the same.
\end{example}

\subsubsection{Quoting functions}\label{sec:lit-reflection-functions}

The |Definition| type also has a constructor for function definitions
which has a |FunctionDef| argument.
|FunctionDef| consists of the type of the function and a list of
clauses.
Each clause has a |Pattern| for each argument, and a Term if it is not
an absurd clause.

\begin{code}
data FunctionDef : Set where
  fun-def : Type → List Clause → FunctionDef
data Clause : Set where
  clause        : List (Arg Pattern) → Term → Clause
  absurd-clause : List (Arg Pattern) → Clause
\end{code}

Notably absent are rewrite/with-clauses and the |where| keyword.
All of these are quoted as calls to a separate function.

\begin{example}
Consider the following three variants of |add2|, which all add two to
some number:

\begin{code}
add2-with : ℕ → ℕ
add2-with n with suc n
add2-with n | 1+n = suc 1+n

add2-where : ℕ → ℕ
add2-where n = add1 (suc n)
  where add1 : ℕ → ℕ
        add1 1+n = suc 1+n

add1 : ℕ → ℕ → ℕ
add1 n 1+n = suc 1+n
add2-ext : ℕ → ℕ
add2-ext n = add1 n (suc n)
\end{code}

All these variants will look the same when seen through the reflection
mechanism, except for a different name of the inner function.
For example, |definition (quote add2-with)| contains something like
|def (quote .MyModule.with-74) (⋯)|, representing a call to a function
with the automatically generated name |.MyModule.with-74|.
The definition of that function can be retrieved by using that |Name|
directly.
\end{example}

It is also possible to define new functions from a |FunctionDef| using
|unquoteDecl|.

\begin{code}
unquoteDecl x = fdef
\end{code}

In this case, |x| is the name we are defining and |fdef| is a term
which normalizes to a |FunctionDef|.
Within |fdef|, |x| is available as a value of type |Name| to allow
recursive functions.
One might, for instance, use the following pattern:

\begin{code}
f : Name → FunctionDef
f = ?
unquoteDecl x = f x
\end{code}

\begin{remark}
|unquoteDecl| is the only construct in the reflection mechanism which
introduces a new defined name in the environment.
Other kinds of definitions like datatypes and records can not be
unquoted.
Functions with rewrite-clauses, with-clauses or |where|s introduce
extra names, so they must use multiple |unquoteDecl|s.
\end{remark}

\subsection{Ornaments}\label{sec:lit-ornaments}

When two algebraic datatypes have a similar recursive structure,
ornaments can be used to specify the exact relation between those two
types.
Ornaments are structure-preserving transformations which can take two
forms: \emph{extension} and \emph{refinement}.

\subsubsection{Extension}\label{sec:lit-extensions}

Extensions attach extra information to some of the constructors of a
datatype.

\begin{example}
A typical example of extending is the nat→list ornament.
Compare the two datatypes, in indexfirst style:

\begin{code}
indexfirst data ℕ : Set where
  ℕ ∋ zero
    | suc (n : ℕ)

indexfirst data List (A : Set) : Set where
  List A ∋ []
          | _∷_ (a : A) (as : List A)
\end{code}

Now we can transform |ℕ| to |List| by inserting an |a : A| at each
successor node.
(We do not mind about the exact names of the datatype and
constructors.)
\end{example}

In a simple universe with support for constants we could implement
extensions using the following datatype, indexed by the description
which is being ornamented:

\begin{code}
data Orn : (D : Desc) → Set₁ where
  `0 : Orn `0
  `1 : Orn `1
  _`+_ : ∀{A B} → Orn A → Orn B → Orn (A `+ B)
  _`*_ : ∀{A B} → Orn A → Orn B → Orn (A `* B)
  `var : Orn `var
  `K : {S : Set₀} → Orn (`K S)
  _insert*_ : (A : Desc){B : Desc} → Orn B → Orn B
\end{code}

Most of the constructors mean that the structure of the original
description must be copied.
|_insert*_| is an ornament on a description |B|, and inserts a
description |A| using |_`*_|.
We can define the following semantics for ornaments:

\begin{code}
⟦_⟧orn : {D : Desc} → Orn D → Desc
⟦ `0 ⟧orn = `0
⟦ `1 ⟧orn = `1
⟦ A `+ B ⟧orn = ⟦ A ⟧orn `+ ⟦ B ⟧orn
⟦ A `* B ⟧orn = ⟦ A ⟧orn `* ⟦ B ⟧orn
⟦ `var ⟧orn = `var
⟦ `K {S} ⟧orn = `K S
⟦ A insert* B ⟧orn = A `* ⟦ B ⟧orn
\end{code}

\begin{example}
The descriptions of naturals and lists are:

\begin{code}
ℕDesc : Desc
ℕDesc = `1 `+ `var
ListDesc : Set → Desc
ListDesc A = `1 `+ (`K A) `* `var
\end{code}

We can define an ornament from naturals to lists:

\begin{code}
ℕ⇒List : Set → Orn ℕDesc
ℕ⇒List A = `1 `+ (`K A) insert* `var
\end{code}

As expected, the interpretation of the ornament is exactly the
description of lists, so |∀{A} → ⟦ ℕ⇒List A ⟧orn ≡ ListDesc A|.
\end{example}

\subsubsection{Refinement}\label{sec:lit-refinements}

The second form of ornamentation is \emph{refinement}, which adds extra
indices and requirements on those indices.
It essentially restricts what values can be made.

For example, vectors are lists with the addition of an index
indicating the length.

Ornaments supporting refinements work on descriptions which
support indices, so there is a bit more work involved in defining them
properly.
In \cite{dagand14-transporting} a small universe similar to the one in
section \ref{sec:lit-sigmaset} is used, without |_`+_| and |_`*_| but
with |`Σ|.
There the universe of ornaments has a |var| constructor which refines
the index, together with |insert| and |delete| constructors which
together can replace |`Σ|s.

\subsubsection{Algebraic ornaments}

An interesting class of ornaments is that of \emph{algebraic
  ornaments}.
Every |⟦ D ⟧|-algebra, which can be used to fold over a datatype
described by |D|, yields an ornament on |D|.
This ornament indexes |D| by the results of the fold over its
elements.

\begin{example}
One might define a |length|-algebra on lists.
This algebra can be used as an algebraic ornament, which results in a
list datatype which is indexed by its length.
This corresponds exactly to the datatype of vectors\cite{dagand14-transporting}.
\end{example}

\begin{example}
A useful example of algebraic ornaments is given in
\cite{dagand14-transporting}.
Given some datatype for expressions |Expr|, we might define their
semantics using an evaluation algebra |evalAlg|.
This can be used as an algebraic ornament to obtain a datatype of
expressions indexed by their semantics, |Expr^evalAlg|.
With such a datatype, one can define \emph{semantics-preserving
  operations}: |∀ x → Expr^evalAlg x → Expr^evalAlg x|.
A function of that type ensures that the returned expression evaluates
to the same value as the argument expression.
\end{example}

\subsubsection{Defining ornaments by functions}

We have shown how to implement ornaments as the difference between two
|Desc|s.
Alternatively, one can build a system where ornaments are built by
providing a projection function from the ornamented to the base type.
This has been implemented as an extension to a subset of ML
\cite{williams14}.
The system inspects such a function definition and can use it as an
ornament.

For example, by defining the |length| function of type |List A → ℕ|,
the system would be able to extract an ornament.
This ornament can be used to generate a partial function definition of
|++| (append) from the definition of |+|.

This approach is quite intuitive and is easy to understand without
knowing much about ornaments specifically.
There are however significant limitations on the specific shape of the
projection functions which are used as an ornament.
The patterns and terms must have a very specific structure, because
the mapping has to work in both ways.

An important observation to make on this approach is that the
ornamented type can not be generated by the ornament, because the
ornamented type must be defined before an ornament can be built.
The approach of the previous sections does not have this requirement,
and one could make an ornament for a type and generate the ornamented
type from that.
