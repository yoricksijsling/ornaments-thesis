%include lhs2TeX.fmt
%include polycode.fmt

\section{Experimental study: Quoting library}\label{sec:prototype}

For this thesis we will be using quoting in Agda.
We know that the quoting mechanism can be hard to work with, and is
incomplete in some ways.
The quoting mechanism is not well documented and published literature
does not teach us everything there is to know about it.

For this reason, and to get some concrete experience with generic
programming in Agda, we have built a prototype for a quoting library.
The quoting library is able to look at an existing data type and give
a description of it.
It also generates definitions for the embedding-projection pair which
can be unquoted.

\subsection{Universe}

To keep things simple, we have chosen a fairly simple universe for
context-free types with a single fix
point\definedin{ContextFree.One.Desc}.

\subsubsection{Parameters}

Many practical data types have data type parameters, so we wanted to
support this in the library.
Parameters are encoded by introducing the \texttt{`P₀} constructor,
which describes a data type parameter of kind \texttt{Set₀}, resulting
in the following \texttt{Desc} type:

\begin{alltt}
data Desc : Set₁ where
  `P₀ : (S : Set₀) → Desc
  `0 : Desc
  `1 : Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
  `rec : Desc
\end{alltt}

The interpretation of \texttt{`P₀} is simple:

\begin{alltt}
⟦ `P₀ S ⟧ X = S
\end{alltt}

\begin{remark}
We choose \emph{not} to limit the parameters to types which we can
quote to a description.
If the original data type does not impose any restrictions for a
parameter, the description should not impose any restrictions either.
\end{remark}

A drawback of this way of encoding parameters is that \texttt{Desc}
is in \texttt{Set₁}.
Even worse, if we might want to add support for parameters in
\texttt{Set₁} and higher, the level of \texttt{Desc} would increase
too.
The choice for this encoding is mostly pragmatic; it is simply the one
which we have gotten to work.

Alternatively, it might be possible to move the \texttt{Set} argument
to the parameters of \texttt{Desc} and then refer to them in the
constructor:

\begin{alltt}
data Desc {pc : ℕ}(params : Vec Set pc) : Set where
  `P₀ : Fin pc → Desc params
  ...
\end{alltt}

This neatly places \texttt{Desc} in \texttt{Set₀} but it is not
easy to work with.
Up to this point we have not found fundamental reasons why this would
not work, so it is definitely a change to consider in future work.

The quoting library should generate three functions; one which gives
the description within the universe, and two functions which convert
values between the original data type and the interpretation of the
description, commonly referred to as an embedding-projection pair.
All these functions are parameterised by the data type parameters.
A bunch of zero or more parameters is succinctly written as
\texttt{\ttargs{p}}.

\begin{alltt}
desc : (\ttargs{p} : Set₀) → Desc
to : (\ttargs{p} : Set₀) → A → μ (desc \ttargs{p})
from : (\ttargs{p} : Set₀) → μ (desc \ttargs{p}) → A
\end{alltt}

The implementation is correct if \texttt{to} and \texttt{from} are
inverses of each other.

\begin{alltt}
to-from : (\ttargs{p} : Set₀) → ∀ x → from \ttargs{p} (to \ttargs{p} x) ≡ x
from-to : (\ttargs{p} : Set₀) → ∀ x → to \ttargs{p} (from \ttargs{p} x) ≡ x
\end{alltt}

\subsubsection{Examples}

We will first show how we can manually define \texttt{desc},
\texttt{to} and \texttt{from} for some example data types.
The function definitions are picked carefully to have a very
regular structure, so we can generate them automatically later.

\begin{example}[natural numbers]
Natural numbers have two constructors, zero and suc, the first has no
arguments and the latter has one recursive position.
In Agda we would define them with a data
type\definedin{ContextFree.One.Examples.Nat}:

\begin{alltt}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{alltt}

Every data type can be expressed as a sum of products: $\Nat = μX. 1 +
X$.
Each product can freely be terminated with a $1$ and each sum with
$0$, so an equivalent expression is $\Nat = μX. 1 + (X * 1) + 0$.
The $μ$ is implicit in our universe, so we can remove it and use
\texttt{`rec} to refer to the variable which was bound.

\begin{alltt}
desc : Desc
desc = `1 `+ (`rec `* `1) `+ `0
\end{alltt}

We could have omitted the extra \texttt{`1}'s and \texttt{`0}'s, but
this way the structure is more regular.
This is going to be the template for what we want the library to
generate, so a more regular structure will make code generation
simpler.

The definitions of \texttt{to} and \texttt{from} are fairly
straightforward:

\begin{alltt}
to : ℕ → μ desc
to zero = ⟨ inj₁ tt ⟩
to (suc n) = ⟨ inj₂ (inj₁ (to n , tt)) ⟩

from : μ desc → ℕ
from ⟨ inj₁ tt ⟩ = zero
from ⟨ inj₂ (inj₁ (n , tt)) ⟩ = suc (from n)
from ⟨ inj₂ (inj₂ ()) ⟩
\end{alltt}

It is easy to prove that \texttt{to} and \texttt{from} are inverses of
each other.
Those proofs are omitted here, as they are not very interesting.
\end{example}

\begin{example}[trees]
We will take a look at how trees are embedded in our
universe\definedin{ContextFree.One.Examples.Tree}.

\begin{alltt}
data Tree (A : Set) : Set where
  leaf : Tree A
  node1 : A → Tree A → Tree A
  node2 : A → Tree A → Tree A → Tree A
\end{alltt}

Our trees take a type parameter, and the nodes can have one or two
subtrees.
They can alternatively be described as $\Tree A = μX. 1 + A × X + A × X
× X$.
This data structure is chosen specifically to show what happens when
we add type parameters, more than two constructors and multiple
recursive points within a constructor.

\begin{alltt}
desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `rec `* `1) `+ (`P₀ A `* `rec `* `rec `* `1) `+ `0

to : (A : Set) → Tree A → μ (desc A)
to A leaf = ⟨ inj₁ tt ⟩
to A (node1 v xs) = ⟨ inj₂ (inj₁ (v , to A xs , tt)) ⟩
to A (node2 v xs ys) = ⟨ inj₂ (inj₂ (inj₁ (v , to A xs , to A ys , tt))) ⟩

from : (A : Set) → μ (desc A) → Tree A
from A ⟨ inj₁ tt ⟩ = leaf
from A ⟨ inj₂ (inj₁ (v , xs , tt)) ⟩ = node1 v (from A xs)
from A ⟨ inj₂ (inj₂ (inj₁ (v , xs , ys , tt))) ⟩
  = node2 v (from A xs) (from A ys)
from A ⟨ inj₂ (inj₂ (inj₂ ())) ⟩
\end{alltt}
\end{example}

\subsubsection{Structure of embedding-projection pair}

There is a pretty symmetry between the patterns and terms of the
clauses in \texttt{from} and the terms and patterns (respectively) of
the clauses in \texttt{to}.
Take the clauses for \texttt{node1}, the emphasized parts correspond
with each other.

\begin{alltt}
to A (\ttemph1{node1 v} xs) = \ttemph2{⟨ inj₂ (inj₁ (v , }to A xs\ttemph2{ , tt)) ⟩}
from A \ttemph2{⟨ inj₂ (inj₁ (v , }xs\ttemph2{ , tt)) ⟩} = \ttemph1{node1 v} (from A xs)
\end{alltt}

\begin{definition}[to/from symmetry]
An embedding-projection pair has \emph{to/from symmetry} when for each
constructor of the datatype we can pick pattern
synonyms\footnote{It works like this if pattern synonyms would not
  check for unbound variables like \texttt{v} in the \texttt{node1}
  constructor.
  Agda's pattern synonyms do check this, so to implement this all free
  variables have to be bound, slightly complicating the definitions in
  this section.}
α and β such that \texttt{to} and \texttt{from} contain the following
clauses:

\begin{alltt}
to \ttargs{p} (\ttemph1{α} x₁⋯xₙ) = \ttemph2{β} (to \ttargs{p} x₁)⋯(to \ttargs{p} xₙ)
from \ttargs{p} (\ttemph2{β} y₁⋯yₙ) = \ttemph1{α} (from \ttargs{p} y₁)⋯(from \ttargs{p} yₙ)
\end{alltt}
\end{definition}

To fully define the embedding-projection pair, we only have to give
suitable definitions for \texttt{α} and \texttt{β} for every
constructor.
The pattern synonyms for the $i$th constructor (starting with $i=0$)
will look something like this:

\begin{alltt}
αᵢ = constructorᵢ x₁⋯xₙ
βᵢ = ⟨ inj₂ⁱ (inj₁ (x₁ , ⋯ , xₙ , tt)) ⟩
\end{alltt}

Where \texttt{inj₂ⁱ} is exactly $i$ applications of \texttt{inj₂}.
This is a simplified representation, but it should give the reader
an idea what the structure is.

\begin{theorem}
When an embedding-projection pair has to/from symmetry, \texttt{from}
and \texttt{to} are each others inverses.
\end{theorem}
\begin{proof}


The degenerate case without recursive arguments (for instance for
\texttt{leaf}) is trivial:

\begin{alltt}
to \ttargs{p} (from \ttargs{p} β) ≡ to \ttargs{p} α ≡ β
from \ttargs{p} (to \ttargs{p} α) ≡ from \ttargs{p} β = α
\end{alltt}

To prove that \texttt{to \ttargs{p} (from \ttargs{p} (β y₁⋯yₙ)) ≡ β
  y₁⋯yₙ} we use induction.

\begin{alltt}
to \ttargs{p} (from \ttargs{p} (β y₁⋯yₙ))
  ≡ (definition of from)
to \ttargs{p} (α (from \ttargs{p} y₁)⋯(from \ttargs{p} yₙ))
  ≡ (definition of to)
β (to \ttargs{p} (from \ttargs{p} y₁))⋯(to \ttargs{p} (from \ttargs{p} yₙ))
  ≡ (induction hypotheses: to \ttargs{p} (from \ttargs{p} y₁) ≡ y₁ and so forth)
β y₁⋯yₙ
\end{alltt}

The induction terminates because we are using structurally smaller
arguments in every step.
A similar argument can be used to show that
\texttt{from \ttargs{p} (to \ttargs{p} (α x₁⋯xₙ)) ≡ α x₁⋯xₙ}.
\end{proof}

So we know that as long as the embedding-projection pair is built such
that it has to/from symmetry, we should always be able to prove that
\texttt{to} and \texttt{from} are inverses.
In fact, the patterns \texttt{α} and \texttt{β} can be reused to give
the clauses for \texttt{to-from} and \texttt{from-to}:

\begin{alltt}
to-from \ttargs{p} (α x₁⋯xₙ) = congₙ α (to-from \ttargs{p} x₁) ⋯ (to-from \ttargs{p} xₙ)
from-to \ttargs{p} (β x₁⋯xₙ) = congₙ β (from-to \ttargs{p} x₁) ⋯ (from-to \ttargs{p} xₙ)
\end{alltt}

Where \texttt{congₙ} is of type
\texttt{(f : A₁ → ⋯ → Aₙ → B) → x₁ ≡ y₁ → ⋯ → xₙ ≡ yₙ → f x₁ ⋯ xₙ ≡ f y₁ ⋯ yₙ}
for the right implicit variables.
The generation of the function definitions for \texttt{to-from} and
\texttt{from-to} are not implemented in the prototype.

\subsection{Implementation}\label{sec:prototype-implementation}

Up to this point we have not shown much of the technical
details of the prototype quoting library.
In the next section we describe an intermediate representation closely
related to \texttt{Desc}.

The quoting process is then split in roughly two parts:
\begin{enumerate}
\item Quoting the datatype to the intermediate representation,
  explained in section \ref{sec:prototype-quoting}.
\item Using the intermediate representation to generate the
  description and the definitions of \texttt{to} and \texttt{from},
  which is described in section \ref{sec:prototype-unquoting}.
\end{enumerate}

\subsubsection{SafeDatatype}\label{sec:prototype-safedatatype}

The intermediate representation
\texttt{SafeDatatype}\definedin{ContextFree.One.Quoted} is chosen to
be safe in the sense that we can always convert it to a function of
type \texttt{desc : (\ttargs{p} : Set₀) → Desc}.
We have seen how we always generate descriptions in sum-of-products
style, so \texttt{SafeDatatype} is roughly the same as a list of lists
of arguments.

\begin{alltt}
data SafeArg {pc : ℕ} : Set where
  Spar : Fin pc → SafeArg
  Srec : SafeArg
SafeProduct {pc} = List (SafeArg {pc})
SafeSum {pc} = List (SafeProduct {pc})
record SafeDatatype : Set where
  constructor mk
  field pc : ℕ
        params : Vec Param pc
        sop : SafeSum {pc}
\end{alltt}

In the \texttt{SafeDatatype} record, \texttt{pc} is the number of
parameters (\emph{p}arameter \emph{c}ount).
References to parameters with \texttt{Spar} use a De Bruijn index
which is \texttt{pc} at maximum.
The vector of \texttt{Param}s can be used for additional information
for each parameter, currently this is only the visibility of the
parameter but in the future it might be used to specify whether the
type of the parameter is in \texttt{Set₀} or \texttt{Set₁} et cetera.

The \texttt{SafeDatatype} for the Tree example of section
\ref{sec:prototype-trees} looks like this:

\begin{alltt}
treeSdt : SafeDatatype
treeSdt = mk 1 (param₀ visible ∷ [])
               ([] ∷
                (Spar zero ∷ Srec ∷ []) ∷
                (Spar zero ∷ Srec ∷ Srec ∷ []) ∷ [])
\end{alltt}

We have defined a function
\texttt{descFun}\definedin{ContextFree.One.DescFunction} which takes a 
\texttt{SafeDatatype} and the data type parameters to return a Desc.
The type of \texttt{descFun} is dependent on the declared parameters
in the \texttt{SafeDatatype}.
Applied to \texttt{treeSdt}, this function is pointwise equal to
\texttt{desc} of section \ref{sec:prototype-trees}.

\begin{alltt}
treeDesc : Set → Desc
treeDesc A = descFun treeSdt A

testTreeDesc : ∀ A → descFun treeSdt A ≡
  (`1 `+ `P₀ A `* `rec `* `1 `+ `P₀ A `* `rec `* `rec `* `1 `+ `0)
testTreeDesc A = refl
\end{alltt}

Currently, we can not build a function which converts any
\texttt{Desc} to a \texttt{SafeDatatype}.
This is inherently impossible because \texttt{Desc} can be used to
describe types which do not correspond to a single Agda data type.
\todo{Explain more}

\subsubsection{Unquoting}\label{sec:prototype-unquoting}

\texttt{SafeDatatype} does not include any quoted names (or terms), so
it is completely independent of the original datatype.
While this is sufficient for \texttt{descFun}, we will need the name
of the data type and the names of the constructors to be able to
generate the definitions for the embedding-projection pair.
For this purpose we have defined \texttt{NamedSafeDatatype}.

\begin{alltt}
NamedSafeProduct {pc} = (Name × List (SafeArg {pc}))
NamedSafeSum {pc} = List (NamedSafeProduct {pc})
record NamedSafeDatatype : Set where
  constructor mk
  field dtname : Name
        pc : ℕ
        params : Vec Param pc
        sop : NamedSafeSum {pc}
\end{alltt}

Agda's reflection mechanism supports unquoting of function definitions
with \texttt{unquoteDecl}.
To do this, we need a \texttt{FunctionDef}\footnote{All the quoted
  things are built-in in Agda, we will be using the names they are
  given in the standard library.} containing the quoted type and
clauses.

To make recursive references and references to the \texttt{desc}
function, we have to pass the names of \texttt{desc} and
\texttt{to}/\texttt{from} to whichever function creates the function
definition.
All other names used in the function definitions are either in
\texttt{SafeDatatype}, or globally available anyway (like \texttt{μ}
and \texttt{\_,\_}).

\begin{alltt}
makeTo : (`to `desc : Name) → NamedSafeDatatype → FunctionDef
makeFrom : (`from `desc : Name) → NamedSafeDatatype → FunctionDef
\end{alltt}

\texttt{makeTo} and \texttt{makeFrom} generate the function
definitions, now we can unquote them.

\begin{alltt}
unquotedecl to = makeTo to (quote desc) namedsafedatatype
unquotedecl from = makeFrom from (quote desc) namedsafedatatype
\end{alltt}

\begin{remark}
In the current implementation we are not making full use of the fact
that we have to/from-symmetry.
\todo{Make unquoting nicer by using to/from-symmetry and explain a bit
  more about the implementation.}
\end{remark}

\subsubsection[Quoting]{Quoting\definedin{ContextFree.One.Quoting}}
\label{sec:prototype-quoting}

We have used the \texttt{NamedSafeDatatype}, but we still have to get
it first.
This is done by quoting an existing data type.

There are many ways the quoting process can fail, so we have defined
an \texttt{Error}\definedin{Data.Error} type which supports logging
and failure.
It is basically a list of messages combined with a Maybe.
\texttt{Error} is an applicative functor and a monad, so we can manage
the complexity quite well.
Here is an example of functions using \texttt{Error}.

\begin{alltt}
getDatatype : Name → Error Data-type
getDatatype n with definition n
getDatatype n | data-type x = return x
getDatatype n | otherwise = log (showName n ++ " is not a data type") >> fail

getConstructors : Name → Error (List Name)
getConstructors n = constructors <\$> getDatatype n
\end{alltt}

Every constructor can be quoted separately to a
\texttt{NamedSafeProduct} with \texttt{quoteConstructor}\definedin{ContextFree.One.Quoting.Constructor}.
The number of parameters is passed explicitly because we can not infer
that from just the type of the constructor.
The parameter count must be lower than or equal to the maximum number
of allowed parameters as calculated by \texttt{paramCount}.

\begin{alltt}
quoteConstructor : (`dt `c : Name)(pc : ℕ)
  (pc≤ : pc ≤ paramCount (type `c)) → Error (NamedSafeProduct {pc})
\end{alltt}

\texttt{quoteConstructor} splits the type of the passed constructor
name into its arguments and tries to convert each one into an
\texttt{Srec} or \texttt{Spar}.
The target is also checked to make sure the user is not trying to use
indices (which are not supported yet).
Applying \texttt{quoteConstructor} to \texttt{suc} indeed gives us the
wanted result \texttt{Srec ∷ []}:

\begin{alltt}
quoteConstructor (quote Nat) (quote suc) 0 z≤n ≡ return (quote suc , Srec ∷ [])
\end{alltt}

Now we can use \texttt{quoteConstructor} to define a function which quotes
a whole data type.

\begin{alltt}
quoteDatatype : (`dt : Name)(pc : ℕ) → Error NamedSafeDatatype
\end{alltt}

Whether \texttt{Error} is ok or has failed is always decidable.
This means we can unwrap the value of the \texttt{Error} by using an
implicit argument which witnesses that it is ok.
When this is used and the quoting fails, the implicit argument can not
be inferred and we get a type error.

\begin{alltt}
quoteDatatype! : (`dt : Name) (pc : ℕ)
  {isOk : True (isOk? (quoteDatatype `dt pc))} → NamedSafeDatatype
quoteDatatype! _ _ {isOk} = fromOk isOk
\end{alltt}

With this definition we can quote data types quite easily.

\begin{alltt}
nsdt : NamedSafeDatatype
nsdt = quoteDatatype! (quote Tree) 1
\end{alltt}

\subsection{Results and discussion}\label{sec:prototype-results}

The current version of the quoting library can be used like this:

\begin{alltt}
nsdt : NamedSafeDatatype
nsdt = quoteDatatype! (quote Tree) 1

desc : DescFun (toSafeDatatype nsdt)
desc = descFun (toSafeDatatype nsdt)
unquoteDecl to = makeTo to (quote desc) nsdt
unquoteDecl from = makeFrom from (quote desc) nsdt
\end{alltt}

Even though it is not the one-liner we would like to have, the last
four lines are always exactly the same so it seems like this could be
automated quite easily.

The intermediate representation allows us to neatly separate quoting
and unquoting.
For the definition of desc we do not even use unquoting, which might
make it easier to reason about operations on \texttt{SafeDatatype}s at
some point. 

\todo{Maybe fuse SafaDatatype and Desc}

As an experiment, the implementation of this library has given
valuable insights in how to proceed with the thesis.
