%include lhs2TeX.fmt
%include polycode.fmt

\section{Literature review}\label{sec:lit}

Ornaments are strongly related to generic programming.
In particular, many current implementations of ornaments work on
generic representation of data types \cite{dagand12,dagand14-essence,dagand14-transporting}.
We will give an overview of generic programming, making use of the
strengths of dependent types in particular.
For our work we will be using reflection, which is discussed in
section \ref{sec:lit-reflection}.
Finally we will describe ornaments in section
\ref{sec:lit-ornaments}.
\todo{everything included?}

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

\subsection{Universe for finite types}

\todo{Example of enumeration?}
Finite types are all those types which have a finite number of
inhabitants.
If the number of inhabitants of a type is $n$, we might say that the
type is isomorphic to |Fin n|, where |Fin n| can
represent all natural numbers up to $n$.

A practical way of describing finite types is by defining them with a
generative grammar\cite{altenkirch06}:

\[
  τ = 0 \mid 1 \mid τ + τ \mid τ * τ
\]

$0$ and $1$ are for the empty and unit type respectively.
$*$ is used for products and $+$ for coproducts (sums).

This can be formalized as a universe construction\cite{martinloef84}
in Agda with the |Desc| data type:

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
results in the type \texttt{(⊤ ⊎ ⊤) × (⊤ ⊎ ⊤)}.
It is easy to verify that every inhabitant of this type corresponds
uniquely to an inhabitant of a pair of two booleans; they are
isomorphic.
\end{example}

A finite type in this universe might be in a strict sum-of-products
form: $(x * ⋯ * x) + ⋯ + (x * ⋯ * x)$, where all $x$es are $0$ or
$1$.
If this is the case, it can be directly interpreted as an algebraic
data type.
The products correspond to constructors, and the factors of those
products correspond to constructor arguments.
If a finite type is not a sum-of-products (for example $\PairOfBools =
(1 + 1) * (1 + 1)$), the correspondence is not so obvious.\todo{ref}

\subsubsection{Isomorphism}

If we have some data type in our host language which corresponds to
some description, we can relate the two by providing an
embedding-projection pair.

\begin{definition}[Embedding-projection pair for finite types]\label{def:ep-pair-finite}
  An \emph{embedding-projection pair} is a pair of functions
  translating between the interpretation of a description \texttt{⟦ D
    ⟧} and the corresponding data type \texttt{X}.
  They have the types \texttt{to : X → ⟦ D ⟧} and \texttt{from : ⟦ D ⟧
    → X}.
\end{definition}

To really prove that the data type and the interpretation are
isomorphic, we also need to prove that \texttt{to} and \texttt{from}
are inverses.
This is done with the following functions:

\begin{alltt}
to-from : ∀ x → from (to x) ≡ x
from-to : ∀ x → to (from x) ≡ x
\end{alltt}

Together \texttt{to}, \texttt{from}, \texttt{to-from} and
\texttt{from-to} form an isomorphism (bijection).

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
definition of \AD{Desc} in listing \ref{code:finite-desc} to represent
these operations.
We introduce a \AD{ℕ} index to indicate the number of free variables.

\InsertCode{contextfree-naive-desc}

Now we can describe all the context-free types.
However, an interpretation function \AF{⟦\_⟧} is not so
straightforward.
A naive definition of this function will not be accepted by Agda's
termination checker.
Indeed, when we try to interpret \AF{‵nat} = \AI{‵1} \AI{‵+} \AI{`var}
\AI{zero} we get an expanding term \AF{⟦} \AF{‵nat}
\AF{⟧} = \AR{⊤} \AD{⊎} \AF{⟦} \AF{‵nat} \AF{⟧} = ..

\subsubsection{Using functors}\label{sec:lit-cft-single}

A common solution to this non-termination is by interpreting a
description as a functor, and then taking the fix point.
With this method we always assume an implicit $μ$ in front of
the type, so we remove the explicit \AI{μ}
With this method we get rid of the explicit \AI{μ} constructor in the
description type, because we always assume an implicit $μ$ in front of
it.
The interpretation function \AF{⟦\_⟧} is now of type \AD{Desc} \AY{→}
\AD{Set} \AY{→} \AD{Set}, so it takes a \AD{Desc} and gives us a
\emph{pattern functor} on \AD{Set}.
Taking the fix point of the \AD{Set}-endofunctor gives us a \AD{Set}
we can use, a process known as \emph{tying the knot}.

\InsertCode{contextfree-one-base}

Note that in general fix points do not necessarily terminate, so they
do not pass Agda's termination checker.
Therefore we use a fix point construction specialised to
the interpretation function \AF{⟦\_⟧}.
The termination checker inspects the definition of \AF{⟦\_⟧} to see
that none of the clauses introduce unbounded recursion.

With the addition of \texttt{μ} we have to adjust our notion of
embedding-projection pairs (definition \ref{def:ep-pair-finite}).
\begin{definition}[Embedding-projection pair for context-free types]
  An \emph{embedding-projection pair} is a pair of functions
  translating between the interpretation of a description \texttt{μ D}
  and the corresponding data type \texttt{X}.
  They have the types \texttt{X → μ D} and \texttt{μ D → X}.
\end{definition}

\begin{example}[Description of naturals]
The data type for naturals requires recursion, and can now be
described in our universe with:

\begin{alltt}
natDesc = `1 `+ `var
\end{alltt}

To see how this description relates to the original data type, we give
the embedding-projection pair:

\begin{alltt}
to : ℕ → μ natDesc
to zero = ⟨ inj₁ tt ⟩
to (suc n) = ⟨ inj₂ (to n , tt) ⟩

from : μ natDesc → ℕ
from ⟨ inj₁ tt ⟩ = zero
from ⟨ inj₂ (n , tt) ⟩ = suc (from n)
\end{alltt}
\end{example}

This formalization of context free types is limited in a two ways:
\begin{itemize}
\item It allows only one fix point. Therefore it can only describe types
with a single $μ$ variable binding.
\item \texttt{`var} can only refer to the implicitly bound $μ$, so
  datatype parameters are not supported.
\end{itemize}

\subsection{Universe for indexed functors}
\label{sec:lit-indexed}

In the previous section we described a universe where the
interpretation gives back a functor \texttt{Set → Set}.
In that case, the \texttt{Set} argument is used directly in the
interpretation of \texttt{`var}.
We have already seen how \texttt{`var} can be used to reference
multiple variables by passing in a \texttt{Fin n} in section
\ref{sec:lit-cft}, or more generally \emph{some} index which specifies
what variable to use.

\emph{Indexed descriptions} are parameterized over two sets, an input
type \texttt{I} and an output type \texttt{O}.

\begin{alltt}
data IODesc : Set → Set → Set₁ where
  `0 : ∀{I O} → IODesc I O
  `1 : ∀{I O} → IODesc I O
  _`+_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
  _`*_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
  `var : ∀{I O} → I → IODesc I O
\end{alltt}

An indexed description \texttt{IODesc I O} is interpreted as an
indexed functor \texttt{(I → Set) → (O → Set)}.
If both \texttt{I} and \texttt{O} are \texttt{⊤} this is isomorphic to
a normal functor as in section \ref{sec:lit-cft-single}.

\begin{alltt}
IOFunc : Set → Set → Set₁
IOFunc I O = (I → Set) → (O → Set)

⟦_⟧ : ∀{I O} → IODesc I O → (I → Set) → (O → Set)
⟦_⟧ `0 r o = ⊥
⟦_⟧ `1 r o = ⊤
⟦_⟧ (A `+ B) r o = ⟦ A ⟧ r o ⊎ ⟦ B ⟧ r o
⟦_⟧ (A `* B) r o = ⟦ A ⟧ r o × ⟦ B ⟧ r o
⟦_⟧ (`var I) r o = r I
\end{alltt}

In the interpretation one has available a function \texttt{r : I →
  Set} which returns a type given a \emph{request} of type
\texttt{I}.
There is also a \emph{received} request \texttt{o} which is used as a
selector for which type we must respond with.
We use the term request rather vaguely on purpose because it is used
for different things; which we will explain in the following sections.
For a full implementation of this universe we refer the reader to
\cite{loeh11}.

\subsubsection{Parameters}

The request to the function \texttt{r} can be used to refer to
parameters.

\begin{example}
One might describe a datatype for pairs as

\begin{alltt}
PairDesc : IODesc (⊤ ⊎ ⊤) ⊤
PairDesc = `var (inj₁ tt) `* `var (inj₂ tt)
\end{alltt}

In this case the datatype can make requests of type \texttt{⊤ ⊎ ⊤},
while the request it \emph{receives} (\texttt{o}) is just \texttt{⊤}.
We can build a response function which returns a type depending on the
value of the request:

\begin{alltt}
select : (A B : Set) → ⊤ ⊎ ⊤ → Set
select A B (inj₁ tt) = A
select A B (inj₂ tt) = B
\end{alltt}

By interpreting the type we see that for any \texttt{A} and \texttt{B}
\texttt{⟦ PairDesc ⟧ (select A B) tt} evaluates to \texttt{A × B}.
\end{example}

\subsubsection{Recursion}

The \texttt{`var} constructor can also be used for recursive calls.
In that case the request of type \texttt{I} is passed to the data type
itself as the \texttt{o} value, so the input type \texttt{I} must
correspond in some way with the output type \texttt{O}.
If the input and output indices are exactly the same, as in
\texttt{IOFunc O O}, the fixed point is of type \texttt{IOFunc ⊥ O}.
Recursive types may still have parameters, which we will keep outside
of the fixed point, so a functor with parameters of type \texttt{I}
and recursive calls of type \texttt{O} has the type \texttt{IOFunc (I
  + O) O}.

Notice that the indexed functors are closed under fixed points,
contrary to non-indexed functors of type \texttt{Set → Set} which have
\texttt{Set} as their fixed point.
Consequently, we can implement \texttt{`Fix} as a constructor of
\texttt{IODesc}, allowing us to have multiple fixed points within a
data type.

\begin{alltt}
`Fix : ∀{I O} → IODesc (I ⊎ O) O → IODesc I O
\end{alltt}

The interpretation of \texttt{`Fix} uses a new \texttt{μ} datatype
which represents a fixed point on the output indices \texttt{O} but it
does not touch the parameters \texttt{I}.
An implementation of this is found in \cite{loeh11}.

\begin{alltt}
⟦_⟧ (`Fix F) r o = μ F r o
\end{alltt}

\begin{example}
With recursion in place we can now describe Lists in this universe.
Recall the representation of lists: $\List = λA. μX. 1 + A * X$.
The part under the $μ$ has two unbound variables and returns
one type.
This is represented with a description of type \texttt{IODesc (⊤ ⊎ ⊤) ⊤}.
By binding the $X$ with a fixed point a description of type
\texttt{IODesc ⊤ ⊤} is left:

\begin{alltt}
ListFDesc : IODesc (⊤ ⊎ ⊤) ⊤
ListFDesc = `1 `+ (`var (inj₁ tt) `* `var (inj₂ tt))

ListDesc : IODesc ⊤ ⊤
ListDesc = `Fix ListFDesc
\end{alltt}

Every list can be translated to a description:

\begin{alltt}
fromList : ∀{A} → List A → ⟦ ListDesc ⟧ (λ _ → A) tt
fromList [] = ⟨ inj₁ tt ⟩
fromList (x ∷ xs) = ⟨ inj₂ (x , fromList xs) ⟩
\end{alltt}
\end{example}


\subsubsection{Mutually recursive datatypes}

Indexed fixed points are suitable to express families of mutually
recursive data types \cite{yakushev09}.
The request is then used to select which data type to use.

\begin{example}[Trees]
A simple mutually recursive family is the one for trees where each
node has an arbitrary number of subtrees:

\begin{alltt}
mutual
  data Tree (A : Set) : Set where
    empty : Tree A
    node : A → Forest A → Tree A
  data Forest (A : Set) : Set where
    nil : Forest A
    cons : Tree A → Forest A → Forest A
\end{alltt}

We introduce an enumeration type \texttt{WoodTag} to indicate the two
types.
This is not entirely necessary as any type with two inhabitants would
suffice.

\begin{alltt}
data WoodTag : Set where
  tree forest : WoodTag
\end{alltt}

Within the descriptions of both types we can reference the parameter
\texttt{A} and the datatypes \texttt{Tree} and \texttt{Forest}.
This is indicated with the type of the input index: \texttt{⊤ ⊎
  WoodTag}.
The separate types can be described in the normal way:

\begin{alltt}
TreeDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
TreeDescF = `1
         `+ `var (inj₁ tt) `* `var (inj₂ forest)

ForestDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
ForestDescF = `1
           `+ `var (inj₂ tree) `* `var (inj₂ forest)
\end{alltt}

These descriptions now have to be combined in some way, where we use
the output index of type \texttt{WoodTag} to pick the right one.
\end{example}

We do not yet have any constructor of \texttt{IODesc} which uses the
output index of type \texttt{O}.
A simple solution is to introduce a constructor \texttt{`!}; it takes
a value of type \texttt{O}:

\begin{alltt}
`! : ∀{I O} → O → IODesc I O
\end{alltt}

It is interpreted with an equality matching the provided value with
the actual value of \texttt{o}, imposing a \emph{constraint} on the
datatype.

\begin{alltt}
⟦_⟧ (`! o′) r o = o ≡ o′
\end{alltt}

\begin{example}[Trees continued]\label{ex:trees2}
Using the \texttt{`!} constructor we can combine the descriptions of
\texttt{Tree} and \texttt{Forest}.
We basically add a constraint to each description, and then sum them
together.

\begin{alltt}
WoodDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
WoodDescF = `! tree `* TreeDescF
         `+ `! forest `* ForestDescF

WoodDesc : IODesc ⊤ WoodTag
WoodDesc = `Fix WoodDescF
\end{alltt}

The presence of the absurd patterns in the definitions of
\texttt{toTree} and \texttt{toForest} shows how the constraint can not
be solved when the wrong branch is picked:

\begin{alltt}
toTree : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) tree → Tree A
toTree ⟨ inj₁ (refl , inj₁ tt) ⟩ = empty
toTree ⟨ inj₁ (refl , inj₂ (x , f)) ⟩ = node x (toForest f)
toTree ⟨ inj₂ (() , _) ⟩
toForest : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) forest → Forest A
toForest ⟨ inj₁ (() , _) ⟩
toForest ⟨ inj₂ (refl , inj₁ tt) ⟩ = nil
toForest ⟨ inj₂ (refl , inj₂ (t , f)) ⟩ = cons (toTree t) (toForest f)
\end{alltt}
\end{example}

\subsubsection{Indices}

Representing inductive families is essentially the same problem as
representing mutually recursive families.
This is exemplified by the fact that we could have rewritten the mutually
recursive family of example \ref{ex:trees2} to an isomorphic inductive family:

\begin{alltt}
data Wood (A : Set) : WoodTag → Set where
  empty : Wood A tree
  node  : A → Wood A forest → Wood A tree
  nil   : Wood A forest
  cons  : Wood A tree → Wood A forest → Wood A forest
\end{alltt}

Given this definition it is not immediately obvious why the description 
would first split on the index as in example \ref{ex:trees2}.

To understand how inductive families are described in our
universe, it is instructive to use \emph{index-first} notation
\cite{ko11}.
The usual interpretation of Agda datatypes is that the index of the
result type is computed from the chosen constructor and its
arguments.
For example, if we choose to use the \texttt{empty} constructor of the
\texttt{Wood} datatype the index is going to be \texttt{tree}.
This perspective can be turned around:
We might say that \emph{if} we want to create a \texttt{Wood A tree}
\emph{then} we can only use the constructors \texttt{empty} and
\texttt{node}.
Index-first notation emphasizes this way of thinking.
The \texttt{Wood} datatype is written as follows:

\begin{alltt}
indexfirst data Wood (A : Set) : WoodTag → Set where
  Wood A tree   ∋ empty
                | node   (x : A) (f : Wood A forest)
  Wood A forest ∋ nil
                | cons   (t : Wood A tree) (f : Wood A forest)
\end{alltt}

By writing it this way, it becomes obvious that we first have to
look at the required index, before determining what description to use.

\todo{alternative solutions, matching on the o as in 'transporting
  functions'?, Σ is an alternative?}

\subsection{Using other types}

Consider lists of naturals: $\NatList = μX. 1 + ℕ * X$.
Notice that we reference another type $ℕ$ here.
Up to this point, our universes do not have a way to represent this
directly.
In the universe for indexed functors we could replace $ℕ$ by its
description giving us $\NatList = μX. 1 + (μY. 1 + Y) * X$; this
relies on the ability to represent nested fixed points.
If the universe does not allow nested fixed points we need another
way.

\subsubsection{Constants}\label{sec:lit-constants}

The classic way to do this is by introducing a \texttt{`K}
constructor.
Starting with the universe of section \ref{sec:lit-cft-single} we add
the following constructor:

\begin{alltt}
`K : (S : Set) → Desc
\end{alltt}

The interpretation of \texttt{`K} is the constant functor:

\begin{alltt}
⟦ `K S ⟧ X = S
\end{alltt}

Do note that this variant of \texttt{`K} only supports constants of
sort \texttt{Set₀}.
It is not possible to make the constructor level-polymorphic, because
the level of the datatype would then depend on a constructor argument,
which is not allowed in Agda.

This constructor conveniently supports inclusion of arbitrary
user-defined datatypes, but it introduces problems too.
Most importantly, some functions such as decidable equality become
impossible to define because we do not know anything about the
included type \cite{loeh11}.

\subsubsection{Rewriting by isomorphism}

In universes where we do have multiple fixed points, we prefer not to
use \texttt{`K}.
However, it can be useful to clarify that there is some connection
between $μY. 1 + Y$ and $ℕ$.
We can do this using the \texttt{`Iso} constructor \cite{loeh11},
which we define for the universe for indexed functors of section
\ref{sec:lit-indexed}:

\begin{alltt}
`Iso : ∀{I O} → (C : IODesc I O) → (D : IOFunc I O)
       ((r : I → Set) → (o : O) → D r o ≃ ⟦ C ⟧ r o) → IODesc I O
\end{alltt}

Here the \texttt{\_≃\_} can be read as 'is isomorphic to', so the
interpretation of the description and the given indexed functor are
isomorphic.
The interpretation uses the indexed functor to return a type.

\begin{alltt}
⟦_⟧ (`Iso C D) r o = D r o
\end{alltt}

\begin{example}
We can define the description of naturals:

\begin{alltt}
ℕDesc : IODesc ⊥ ⊤
ℕDesc = `Fix (`1 `+ `var (inj₂ tt))

ℕDescIso : IODesc ⊥ ⊤
ℕDescIso = `Iso ℕDesc (λ _ _ → ℕ) ℕDesc-iso
\end{alltt}

The interpretation of the type, \texttt{⟦ ℕDescIso ⟧ (λ ()) tt}, is
now \texttt{ℕ}.
It effectively hides what the description looks like and thereby
improves the reusability of defined description.
\end{example}

\subsubsection{Σ using Set}

The description types we have seen all have sums and products using
$+$ and $*$.
In dependently typed languages we have \texttt{Σ}-types, which can be
interpreted as both sums and products \cite{chapman10}.

The type \texttt{Σ[ x ∈ A ] B x } can be seen as a product of
\texttt{A} and \texttt{B x}, which matches with the \texttt{\_`*\_}
constructor.
Alternatively, it can function as a sum of an arbitrary number of
types; a chain of \texttt{\_`+\_}es
In that case \texttt{x} is used to select a position, and the type on
that position is \texttt{B x}.

With this knowledge, we could have defined a universe with the same
functionality as the one in section \ref{sec:lit-cft-single} as such:

\begin{alltt}
data Desc : Set where
  `1 : Desc
  `Σ : (S : Set) → (D : S → Desc) → Desc
  `var : Desc
\end{alltt}

Which is interpreted as a \texttt{Σ}-type:

\begin{alltt}
⟦_⟧ (`Σ S D) X = Σ S (λ s → ⟦ D s ⟧ X)
\end{alltt}

Interestingly, the \texttt{`Σ} also replaces \texttt{`K} and
\texttt{`0}:

\begin{alltt}
`K_`*_ : (S : Set) → Desc → Desc
`K S `* D = `Σ S (λ _ → D)

`0 : Desc
`0 = `Σ ⊥ ⊥-elim
\end{alltt}

\begin{example}
Now list of naturals can be defined as a sigma-of-sigmas:

\begin{alltt}
natlist : Desc
natlist = `Σ (⊤ ⊎ ⊤) (λ { (inj₁ tt) → `1
                        ; (inj₂ tt) → `K ℕ `* `var
                        })
\end{alltt}
\end{example}

\subsubsection{Σ using descriptions}

The \texttt{`Σ} defined in the previous section uses a \texttt{Set} as
the first argument.
This has the same drawbacks as using a \texttt{Set} for
\texttt{`K} (see section \ref{sec:lit-constants}).
This can be avoided by restricting the argument to descriptions.
We define the constructor in the indexed functor universe:

\begin{alltt}
`Σ : ∀{I O} → {C : IODesc ⊥ ⊤} →
     (f : ⟦ C ⟧ (λ _ → ⊤) tt → IODesc I O) → IODesc I O
\end{alltt}

The interpretation

\begin{alltt}
⟦_⟧ (`Σ f) r o = ∃ (λ i → ⟦ f i ⟧ r o)
\end{alltt}

\todo{bla}

\subsection{Containers}

Discuss the semantic approach with containers/signatures.

\subsection{Reflection}\label{sec:lit-reflection}

Agda supports quoting through a few built-in constructs.
There are primitives to get the type and definition of a given name:

\begin{alltt}
type         : Name → Type
definition   : Name → Definition
\end{alltt}

To use them, you need a \texttt{Name} which you can get with the
\texttt{quote} keyword.
A \texttt{Definition} can be anything which has a name, like
functions, data types, records or constructors.
If the definition gives us a data type, we can use 
\texttt{constructors : Data-type → List Name} to get a list of names
of the associated constructors.

\todo{no visible difference between parameters and indices}

unquotedecl...

\todo{much more}

\subsection{Ornaments}\label{sec:lit-ornaments}

When two algebraic data types have a similar recursive structure,
ornaments can be used to specify the exact relation between those two
types.

\subsubsection{Extending}

'Insert' an argument somewhere in a product \cite{dagand14-transporting}.
'Delete' is related to this.
\todo{example of nat→list ornament}

\subsubsection{Refining}

Change indices of inductive points (var).
\todo{example of list→vec and nat→fin ornaments}

\subsubsection{Ornaments from functions}

We have shown how to implement ornaments as the difference between two
\texttt{Desc}s.
Alternatively, one can build a system where ornaments are built by
providing a projection function from the ornamented to the base type.
This has been implemented as an extension to a subset of ML
\cite{williams14}.
The system inspects such a function definition and can use it as an
ornament to lift functions.

\begin{example}
By simply defining the \texttt{length} function of type \texttt{List A
  → ℕ}, the system would be able to generate a partial function
definition of \texttt{++} (append) from the definition of \texttt{+}.
\end{example}

This approach is quite intuitive and is easy to understand without
knowing much about ornaments specifically.
There are however significant limits on the form of the projection
functions which are used as an ornament, the patterns and terms must
take on a very specific structure.

An important observation to make on this approach is that the
ornamented type can not be generated by the ornament, because the
ornamented type must be defined before an ornament can be built.
The approach of the previous sections does not have this requirement,
and one could make an ornament for a type and generate the ornamented
type from that.

\subsubsection{Uses of ornaments}

\todo{explain more}

\begin{itemize}
\item Lifting functions to reduce code duplication
\item Refactoring
\item Removing constructors
\end{itemize}

\cite{williams14}
