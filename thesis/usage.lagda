%include thesis.fmt

\chapter{Usage}\label{sec:usage}

In this section we provide a short overview of how the whole system
works. It is meant to show how the different components fit together,
so we do not explain all the details. We focus on how an end-user with
minimal knowledge about ornaments or generics would be able to use
this system and explain all the details in later sections.

To start with, we apply the |deriveHasDesc| function to the |Nat|
datatype. This performs all kinds of metaprogramming magic to
introduce two new definitions in the current scope: |quotedNat|
and |NatHasDesc|.

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

unquoteDecl quotedNat NatHasDesc =
  deriveHasDesc quotedNat NatHasDesc (quote Nat)
\end{code}

From our newly obtained |quotedNat| we can retrieve a
\emph{description} which is the representation of a datatype
declaration within the system. The description is of type |Desc ε ε
_|; the arguments |ε| and |ε| indicate that this datatype has no
parameters and no indices. For now we are only concerned with the type
of the description; we can use it without actually looking at the
description itself.

\begin{code}
natDesc : Desc ε ε _
natDesc = QuotedDesc.desc quotedNat
\end{code}

The |deriveHasDesc| function has also defined |NatHasDesc| for
us. This is a record instance which contains an embedding-projection
pair. The embedding-projection pair consists of two functions: |from|
and |to|. These functions translate between values of the original
|Nat| type and elements belonging to |natDesc|. |μ natDesc tt
tt| is the |Set| which contains the elements of |natDesc|. We can use
the embedding-projection pair in the following way, note how the
|NatHasDesc| instance is used automatically:

\begin{code}
natTo : Nat → μ natDesc tt tt
natTo = to

natFrom : μ natDesc tt tt → Nat
natFrom = from
\end{code}

Datatypes can also have parameters. A simple example of a datatype
with parameters is |List|. We can use the same |deriveHasDesc|
function to define |quotedList| and |ListHasDesc| automatically. When
we retrieve the description of the datatype we see that it is of type
|Desc ε (ε ▷₁′ Set) _|. The |(ε ▷₁′ Set)| here tells us that there is
one parameter of type |Set|.

\begin{code}
data List (A : Set) : Set where
  nil : List A
  cons : (x : A) → (xs : List A) → List A

unquoteDecl quotedList ListHasDesc =
  deriveHasDesc quotedList ListHasDesc (quote List)

listDesc : Desc ε (ε ▷₁′ Set) _
listDesc = QuotedDesc.desc quotedList
\end{code}

The types of the |to| and |from| functions are slightly different this
time, because they have to work for every value of the parameter, so
for all |A| of type |Set|. The |A| has to be passed to both |List| and
|μ listDesc| to obtain proper |Set|s.

\begin{code}
listTo : ∀{A} → List A → μ listDesc (tt , A) tt
listTo = to

listFrom : ∀{A} → μ listDesc (tt , A) tt → List A
listFrom = from
\end{code}

With the |ListHasDesc| instance we can perform generic operations on
|List|s. |gdepth| |: ∀{A} → ⦃ R : HasDesc A ⦄ → A → Nat)| calculates the
depth of any value which has a generic representation. (To be precise,
|gdepth| counts the number of recursive occurences of the datatype
within a value of that type.) For |List|s this is exactly the length
of a list:

\begin{code}
length : ∀{A} → List A → Nat
length = gdepth
\end{code}

The length of a list can also be calculated using a fold and an
algebra. Actually, that is precisely what |gdepth| does internally. It
uses an algebra |depthAlg listDesc| and folds it over the list. One
may also define the|length| function as follows:

\begin{code}
length′ : ∀{A} → List A → Nat
length′ = gfold (depthAlg listDesc)
\end{code}

We have taken a look at naturals and lists. These datatypes are
similar in their recursive structure and we want to exploit that. We
can create a so-called ornament which can be used as a patch on the
description of naturals to get the description of lists. Descriptions
do not include names of the datatype and constructors, but they do
include names of arguments so we have to do two things to obtain lists
from naturals:

\begin{itemize}
\item The recursive argument of suc must be renamed to
  |"xs"|. |renameArguments| |1 (just "xs" ∷ [])| gives an ornament which
  does that.
\item A parameter of type |Set| must be added, and be used as an
  argument of in the suc/cons constructor. The ornament to do that is
  |addParameterArg 1 "x"|.
\end{itemize}

These two ornaments have to be applied in sequence, so they are
composed using |>>⁺|. The resulting ornament can be applied using
|ornToDesc|, and we see that |ornToDesc nat→list| results in a
description which is exactly the same as |listDesc|:

\begin{code}
nat→list : Orn _ _ natDesc
nat→list = renameArguments 1 (just "xs" ∷ [])
  >>⁺ addParameterArg 1 "x"

test-nat→list : ornToDesc nat→list ≡ listDesc
test-nat→list = refl
\end{code}

Datatype indices can be used to \emph{refine} datatypes. Such a
refinement can ensure that values can only be built if they adhere to
a certain invariant. For instance, a length index can be added to lists
to ensure that only lists of the specified length are allowed. One
class of ornaments which introduces indices is that of \emph{algebraic
  ornaments}. These use an algebra on the original datatype to
calculate the values of the indices. |depthAlg listDesc| is the
algebra which calculates the length of lists, and we can use |algOrn|
to build an ornament based on that algebra:

\begin{code}
list→vec : Orn _ _ listDesc
list→vec = algOrn (depthAlg listDesc)
\end{code}

As expected, this ornament results in a description with an index of
type |Nat|. The list of indices is now |(ε ▷′ Nat)|, and the list of
parameters is still |(ε ▷₁′ Set)|.

\begin{code}
vecDesc : Desc (ε ▷′ Nat) (ε ▷₁′ Set) _
vecDesc = ornToDesc list→vec
\end{code}

We have built a new description using ornamentation, but it does not
correspond to any datatype yet. Our descriptions are defined in such a
way that they can always be converted back to a real datatype
definition. The reflection mechanism in Agda does not yet support the
definition of datatypes, but we \emph{can} calculate what the type of
the datatype and each constructor has to be. We do have to write the
skeleton of the datatype definition, but not the types
themselves. Using |deriveHasDescExisting| we can derive |VecHasDesc|
which connects the datatype |Vec| to the existing description
|vecDesc|, so the |to| and |from| functions go between |Vec A n| and
|μ vecDesc (tt , A) (tt , n)|.

\begin{code}
data Vec (A : Set) : unquoteDat vecDesc where
  nil : unquoteCon vecDesc 0 Vec
  cons : unquoteCon vecDesc 1 Vec
unquoteDecl quotedVec VecHasDesc =
  deriveHasDescExisting quotedVec VecHasDesc (quote Vec) vecDesc
\end{code}

An essential property of ornaments is that elements of the ornamented
datatype are always at least as informative as the elements of the
original datatype. In other words, each element of the ornamented
datatype can be transformed back to an element of the original
datatype. |gforget| is a generic operation which does that for a given
ornament. We can use it to define the function which transforms a
|Vec| to the corresponding |List|:

\begin{code}
vecToList : ∀{A n} → Vec A n → List A
vecToList = gforget list→vec
\end{code}

We have shown how we can use our implementation to perform generic
operations and to build and use ornaments on a high level with a
fairly limited amount of knowledge. We did not once have to look at
the descriptions on which all these functions work internally. In the
rest of this thesis we will be taking a better look on how these
descriptions and ornaments have to be defined and how metaprogramming
can be used to connect the descriptions to actual datatypes.
