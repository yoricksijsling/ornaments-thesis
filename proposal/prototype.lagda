%include proposal.fmt

\section{Experimental study: Quoting library}\label{sec:prototype}

For this thesis we will be using quoting in Agda.
We know that the quoting mechanism can be hard to work with, and is
incomplete in some ways.
The quoting mechanism is not well documented and published literature
does not tell us everything there is to know about it.

For this reason, and to get some concrete experience with generic
programming in Agda, we have built a prototype for a quoting library.
The quoting library is able to look at an existing datatype and give
a description of it.
It also generates definitions for the embedding-projection pair which
can be unquoted.

\subsection{Universe}

To keep things simple, we have chosen a fairly simple universe for
context-free types with a single fix
point\definedin{ContextFree.One.Desc}.

\subsubsection{Parameters}

Many practical datatypes have datatype parameters, so we wanted to
support this in the library.
Parameters are encoded as constants by introducing the |`P₀| constructor.

\begin{code}
data Desc : Set₁ where
  `P₀ : (S : Set₀) → Desc
  `0 : Desc
  `1 : Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
  `rec : Desc
\end{code}

The interpretation of |`P₀| is simple:

\begin{code}
⟦ `P₀ S ⟧ X = S
\end{code}

As discussed in section \ref{sec:lit-constants}, constants have some
drawbacks.
Due to the unability to encode multiple fixed points the ways of
encoding parameters are limited; it is not possible to pass a |Desc|
instead of the |Set₀|.
Once we move to a universe with indexed functors we can get rid of
this constructor and implement parameters as in section
\ref{sec:lit-indexed-parameters}.

The quoting library should provide three functions; one which gives
the description within the universe, and an embedding-projection pair
to convert values between the original datatype and the
interpretation of the description.
All these functions are parameterized by the datatype parameters.
A bunch of zero or more parameters is succinctly written as
|pargs|.

\begin{code}
desc : (pargs : Set₀) → Desc
to : (pargs : Set₀) → A → μ (desc pargs)
from : (pargs : Set₀) → μ (desc pargs) → A
\end{code}

The implementation is correct if |to| and |from| are
inverses of each other.

\begin{code}
to-from : (pargs : Set₀) → ∀ x → from pargs (to pargs x) ≡ x
from-to : (pargs : Set₀) → ∀ x → to pargs (from pargs x) ≡ x
\end{code}

\subsubsection{Examples}\label{sec:lit-desc-examples}

We will first show how we can manually define |desc|, |to| and |from| for some example datatypes.
The function definitions are picked carefully to have a very
regular structure, so we can generate them automatically later.

\begin{example}[natural numbers]
Natural numbers have two constructors, zero and suc, the first has no
arguments and the latter has one recursive position.
In Agda we would define them with a data
type\definedin{ContextFree.One.Examples.Nat}:

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}

Every datatype can be expressed as a sum of products: $\Nat = μX. 1 +
X$.
Each product can freely be terminated with a $1$ and each sum with
$0$, so an equivalent expression is $\Nat = μX. 1 + (X * 1) + 0$.
The $μ$ is implicit in our universe, so we can remove it and use
|`var| to refer to the variable which was bound.

\begin{code}
desc : Desc
desc = `1 `+ (`rec `* `1) `+ `0
\end{code}

We could have omitted the extra |`1|'s and |`0|'s, but
this way the structure is more regular.
This is going to be the template for what we want the library to
generate, so a more regular structure will make code generation
simpler.

The definitions of |to| and |from| are fairly
straightforward:

\begin{code}
to : ℕ → μ desc
to zero = ⟨ inj₁ tt ⟩
to (suc n) = ⟨ inj₂ (inj₁ (to n , tt)) ⟩

from : μ desc → ℕ
from ⟨ inj₁ tt ⟩ = zero
from ⟨ inj₂ (inj₁ (n , tt)) ⟩ = suc (from n)
from ⟨ inj₂ (inj₂ ()) ⟩
\end{code}

It is easy to prove that |to| and |from| are inverses of
each other.
Those proofs are omitted here, as they are not very interesting.
\end{example}

\begin{example}[trees]
We will take a look at how trees are embedded in our
universe\definedin{ContextFree.One.Examples.Tree}.

\begin{code}
data Tree (A : Set) : Set where
  leaf : Tree A
  node1 : A → Tree A → Tree A
  node2 : A → Tree A → Tree A → Tree A
\end{code}

Our trees take a type parameter, and the nodes can have one or two
subtrees.
They can alternatively be described as $\Tree A = μX. 1 + A × X + A × X
× X$.
This data structure is chosen specifically to show what happens when
we add type parameters, more than two constructors and multiple
recursive points within a constructor.

\begin{code}
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
\end{code}
\end{example}

\subsubsection{Structure of embedding-projection pair}

There is a pretty symmetry between the patterns and terms of the
clauses in |from| and the terms and patterns (respectively) of
the clauses in |to|.
Take the clauses for |node1|, the emphasized parts correspond
with each other.

%{
%format node1-α = "\codeemph1{node1 v }"
%format <node1-β = "\codeemph2{⟨ inj₂ (inj₁ (v , }"
%format node1-β> = "\codeemph2{ , tt)) ⟩}"

%format α = "\codeemph1{α}"
%format β = "\codeemph2{β}"

\begin{code}
to A (node1-α xs) = <node1-β (to A xs) node1-β>
from A <node1-β xs node1-β> = node1-α (from A xs)
\end{code}

\begin{definition}[to/from symmetry]
An embedding-projection pair has \emph{to/from symmetry} when for each
constructor of the datatype we can pick pattern
synonyms\footnote{It works like this if pattern synonyms would not
  check for unbound variables like |v| in the |node1| constructor.
  Agda's pattern synonyms do check this, so to implement this all free
  variables have to be bound, slightly complicating the definitions in
  this section.}
|α| and |β| such that |to| and |from| contain the following
clauses:

\begin{code}
to pargs (α x₁ ⋯ x_n) = β (to pargs x₁)⋯(to pargs x_n)
from pargs (β y₁ ⋯ y_n) = α (from pargs y₁)⋯(from pargs y_n)
\end{code}
\end{definition}
%}

To fully define the embedding-projection pair, we only have to give
suitable definitions for |α| and |β| for every
constructor.
The pattern synonyms for the $i$th constructor (starting with $i=0$)
will look something like this:

\begin{code}
αᵢ = constructorᵢ x₁ ⋯ x_n
βᵢ = ⟨ inj₂ⁱ (inj₁ (x₁ , ⋯ , x_n , tt)) ⟩
\end{code}

Where |inj₂ⁱ| is exactly $i$ applications of |inj₂|.
This is a simplified representation, but it should give the reader
an idea what the structure is.

\begin{theorem}
When an embedding-projection pair has to/from symmetry, |from|
and |to| are each others inverses.
\end{theorem}
\begin{proof}


The degenerate case without recursive arguments (for instance for
|leaf|) is trivial:

\begin{code}
to pargs (from pargs β) ≡ to pargs α ≡ β
from pargs (to pargs α) ≡ from pargs β = α
\end{code}

To prove that |to pargs (from pargs (β y₁ ⋯ y_n)) ≡ β
  y₁ ⋯ y_n| we use induction.

\begin{code}
to pargs (from pargs (β y₁ ⋯ y_n))
  ≡ (definition of from)
to pargs (α (from pargs y₁)⋯(from pargs y_n))
  ≡ (definition of to)
β (to pargs (from pargs y₁))⋯(to pargs (from pargs y_n))
  ≡ (induction hypotheses: to pargs (from pargs y₁) ≡ y₁ and so forth)
β y₁ ⋯ y_n
\end{code}

The induction terminates because we are using structurally smaller
arguments in every step.
A similar argument can be used to show that
|from pargs (to pargs (α x₁ ⋯ x_n)) ≡ α x₁ ⋯ x_n|.
\end{proof}

So we know that as long as the embedding-projection pair is built such
that it has to/from symmetry, we should always be able to prove that
|to| and |from| are inverses.
In fact, the patterns |α| and |β| can be reused to give
the clauses for |to-from| and |from-to|:

\begin{code}
to-from pargs (α x₁ ⋯ x_n) = cong_n α (to-from pargs x₁) ⋯ (to-from pargs x_n)
from-to pargs (β x₁ ⋯ x_n) = cong_n β (from-to pargs x₁) ⋯ (from-to pargs x_n)
\end{code}

Where |cong_n| is of type
|(f : A₁ → ⋯ → A_n → B) → x₁ ≡ y₁ → ⋯ |
|→ x_n ≡ y_n ||→ f x₁ ⋯ x_n ≡ f y₁ ⋯ y_n|
for the right implicit variables.
The generation of the function definitions for |to-from| and
|from-to| are not implemented in the prototype.

\subsection{Implementation}\label{sec:prototype-implementation}

Up to this point we have not shown much of the technical
details of the prototype quoting library.
In the next section we describe an intermediate representation closely
related to |Desc|.

The quoting process is then split in roughly two parts:
\begin{enumerate}
\item Quoting the datatype to the intermediate representation,
  explained in section \ref{sec:prototype-quoting}.
\item Using the intermediate representation to generate the
  description and the definitions of |to| and |from|,
  which is described in section \ref{sec:prototype-unquoting}.
\end{enumerate}

\subsubsection{SafeDatatype}\label{sec:prototype-safedatatype}

The intermediate representation
|SafeDatatype|\definedin{ContextFree.One.Quoted} is chosen to
be safe in the sense that we can always convert it to a function of
type |desc : (pargs : Set₀) → Desc|.
We have seen how we always generate descriptions in sum-of-products
style, so |SafeDatatype| is roughly the same as a list of lists
of arguments.

\begin{code}
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
\end{code}

In the |SafeDatatype| record, |pc| is the number of
parameters (parameter count).
References to parameters with |Spar| use a De Bruijn index
which is |pc| at maximum.
The vector of |Param|s can be used for additional information
for each parameter, currently this is only the visibility of the
parameter but in the future it might be used to specify whether the
type of the parameter is in |Set₀| or |Set₁| et cetera.

The |SafeDatatype| for the |Tree| example of section
\ref{sec:lit-desc-examples} looks like this:

\begin{code}
treeSdt : SafeDatatype
treeSdt = mk 1 (param₀ visible ∷ [])
               ([] ∷
                (Spar zero ∷ Srec ∷ []) ∷
                (Spar zero ∷ Srec ∷ Srec ∷ []) ∷ [])
\end{code}

We have defined a function
|descFun|\definedin{ContextFree.One.DescFunction} which takes a 
|SafeDatatype| and the datatype parameters to return a Desc.
The type of |descFun| is dependent on the declared parameters
in the |SafeDatatype|.
Applied to |treeSdt|, this function is pointwise equal to
|desc| of the |Tree| example.

\begin{code}
treeDesc : Set → Desc
treeDesc A = descFun treeSdt A

testTreeDesc : ∀ A → descFun treeSdt A ≡
  (`1 `+ `P₀ A `* `rec `* `1 `+ `P₀ A `* `rec `* `rec `* `1 `+ `0)
testTreeDesc A = refl
\end{code}

\begin{remark}
While every |SafeDatatype| has a corresponding |Desc|, not every
|Desc| has a corresponding |SafeDatatype|.
\end{remark}

\subsubsection{Unquoting}\label{sec:prototype-unquoting}

|SafeDatatype| does not include any quoted names (or terms), so
it is completely detached from the original datatype.
While this is sufficient for |descFun|, we will need the name
of the datatype and the names of the constructors to be able to
generate the definitions for the embedding-projection pair.
For this purpose we have defined |NamedSafeDatatype|.

\begin{code}
NamedSafeProduct {pc} = (Name × List (SafeArg {pc}))
NamedSafeSum {pc} = List (NamedSafeProduct {pc})
record NamedSafeDatatype : Set where
  constructor mk
  field dtname : Name
        pc : ℕ
        params : Vec Param pc
        sop : NamedSafeSum {pc}
\end{code}

Agda's reflection mechanism supports unquoting of function definitions
with |unquoteDecl|.
To do this, we need a |FunctionDef|\footnote{All the quoted
  things are built-in in Agda, we will be using the names they are
  given in the standard library.} containing the quoted type and
clauses.

To make recursive references and references to the |desc|
function, we have to pass the names of |desc| and
|to|/|from| to whichever function creates the function
definition.
All other names used in the function definitions are either in
|SafeDatatype|, or globally available anyway (like |μ|
and |_,_|).

\begin{code}
makeTo : (`to `desc : Name) → NamedSafeDatatype → FunctionDef
makeFrom : (`from `desc : Name) → NamedSafeDatatype → FunctionDef
\end{code}

|makeTo| and |makeFrom| generate the function
definitions, now we can unquote them.

\begin{code}
unquoteDecl to = makeTo to (quote desc) namedsafedatatype
unquoteDecl from = makeFrom from (quote desc) namedsafedatatype
\end{code}

\begin{remark}
In the current implementation we are not yet making full use of the
fact that we have to/from-symmetry.
We use some functions which can return either a pattern or a term,
depending on the context, but we do not have it everywhere where it is
possible.
\end{remark}

\subsubsection[Quoting]{Quoting\definedin{ContextFree.One.Quoting}}
\label{sec:prototype-quoting}

We have used the |NamedSafeDatatype|, but we have not shown how to get
it.
This is done by quoting an existing datatype.

There are many ways the quoting process can fail, so we have defined
an |Error|\definedin{Data.Error} type which supports logging
and failure.
It is basically a list of messages combined with a Maybe.
|Error| is an applicative functor and a monad, so we can manage
the complexity quite well.
Here is an example of functions using |Error|.

\begin{code}
getDatatype : Name → Error Data-type
getDatatype n with definition n
getDatatype n | data-type x = return x
getDatatype n | otherwise = log (showName n ++ " is not a datatype") >> fail

getConstructors : Name → Error (List Name)
getConstructors n = constructors `fmap` getDatatype n
\end{code}

Every constructor can be quoted separately to a
|NamedSafeProduct| with |quoteConstructor|\definedin{ContextFree.One.Quoting.Constructor}.
The number of parameters is passed explicitly because we can not infer
that from just the type of the constructor.
The parameter count must be lower than or equal to the maximum number
of allowed parameters as calculated by |paramCount|.

\begin{code}
quoteConstructor : (`dt `c : Name)(pc : ℕ)
  (pc≤ : pc ≤ paramCount (type `c)) → Error (NamedSafeProduct {pc})
\end{code}

|quoteConstructor| splits the type of the passed constructor
name into its arguments and tries to convert each one into an
|Srec| or |Spar|.
The target is also checked to make sure the user is not trying to use
indices (which are not supported yet).
Applying |quoteConstructor| to |suc| indeed gives us the
wanted result |Srec ∷ []|:

\begin{code}
quoteConstructor (quote Nat) (quote suc) 0 z≤n ≡ return (quote suc , Srec ∷ [])
\end{code}

Now we can use |quoteConstructor| to define a function which quotes
a whole datatype.

\begin{code}
quoteDatatype : (`dt : Name)(pc : ℕ) → Error NamedSafeDatatype
\end{code}

Whether |Error| is ok or has failed is always decidable.
This means we can unwrap the value of the |Error| by using an
implicit argument which witnesses that it is ok.
When this is used and the quoting fails, the implicit argument can not
be inferred and we get a type error.

\begin{code}
quoteDatatype! : (`dt : Name) (pc : ℕ)
  {isOk : True (isOk? (quoteDatatype `dt pc))} → NamedSafeDatatype
quoteDatatype! _ _ {isOk} = fromOk isOk
\end{code}

With this definition we can quote datatypes quite easily.

\begin{code}
nsdt : NamedSafeDatatype
nsdt = quoteDatatype! (quote Tree) 1
\end{code}

\subsection{Results and discussion}\label{sec:prototype-results}

The current version of the quoting library can be used like this:

\begin{code}
nsdt : NamedSafeDatatype
nsdt = quoteDatatype! (quote Tree) 1

desc : DescFun (toSafeDatatype nsdt)
desc = descFun (toSafeDatatype nsdt)
unquoteDecl to = makeTo to (quote desc) nsdt
unquoteDecl from = makeFrom from (quote desc) nsdt
\end{code}

The fact that we can not unquote records or multiple definitions at
once, as remarked in section \ref{sec:lit-reflection-functions}, means
that we will always have to use multiple statements for this process.
Even though it is not the one-liner we would like to have, the last
four lines are always exactly the same so it seems like this could be
automated quite easily.

The intermediate representation allows us to neatly separate quoting
and unquoting.
For the definition of desc we do not even use unquoting, which might
make it easier to reason about operations on |SafeDatatype|s at
some point. 

As an experiment, the implementation of this library has given
valuable insights in how to proceed with the thesis.
Many of the observations described in section \ref{sec:lit-reflection}
come directly from this experiment.