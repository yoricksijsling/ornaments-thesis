%include thesis.fmt

\chapter{Usage}\label{chap:usage}

In this section we provide a short overview of how the generic
programming and ornamentation library works. It is meant to show how
the different components fit together, so not all implementation
details will be presented here. We focus on how an end-user with
minimal knowledge about ornaments or generics would use our
library. The interested reader is asked to suspend their
curiosity---the rest of this thesis explains how the library is
implemented.

To start with, we apply the |deriveHasDesc| function to the |Nat|
datatype. This performs all kinds of meta-programming magic to
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
parameters and no indices. For now we will not be looking at the
description itself.

\begin{code}
natDesc : Desc ε ε _
natDesc = QuotedDesc.desc quotedNat
\end{code}

The |deriveHasDesc| function has also defined |NatHasDesc| for
us. This is a record instance which contains an embedding-projection
pair. The embedding-projection pair translates between values of the
types |Nat| and |μ natDesc tt tt|, where |μ natDesc tt tt| is the
|Set| which contains the elements as described by |natDesc|. The
record is found automatically with instance search, so once
|deriveHasDesc| has been called the embedding-projection can be used
by simply writing |to| or |from|:

\begin{code}
natTo : Nat → μ natDesc tt tt
natTo = to

natFrom : μ natDesc tt tt → Nat
natFrom = from
\end{code}

Datatypes can have parameters. A simple example of a datatype with
parameters is |List|. We can use the same |deriveHasDesc| function to
define |quotedList| and |ListHasDesc| automatically. When we retrieve
the description of the datatype we see that it is of type |Desc ε (ε
▷₁′ Set) _|. The |(ε ▷₁′ Set)| here tells us that there is one
parameter of type |Set|.

\begin{code}
data List (A : Set) : Set where
  nil : List A
  cons : (x : A) → (xs : List A) → List A

unquoteDecl quotedList ListHasDesc =
  deriveHasDesc quotedList ListHasDesc (quote List)

listDesc : Desc ε (ε ▷₁′ Set) _
listDesc = QuotedDesc.desc quotedList
\end{code}

Both |List| and |μ listDesc| are polymorphic in the type of their
elements, so the |to| and |from| functions are now polymorphic as
well:

\begin{code}
listTo : ∀{A} → List A → μ listDesc (tt , A) tt
listTo = to

listFrom : ∀{A} → μ listDesc (tt , A) tt → List A
listFrom = from
\end{code}

With a |HasDesc| instance we can perform generic operations. For
example the function |gdepth| of type |∀{A} → ⦃ R : HasDesc A ⦄ → A →
Nat)| which calculates the depth of any value that has a generic
representation. For the |Nat| type this is just the identity, but for
|List| this is exactly the length of a list:

\begin{code}
nat-id : Nat → Nat
nat-id = gdepth

length : ∀{A} → List A → Nat
length = gdepth
\end{code}

The length of a list can also be calculated using a fold and an
algebra. Actually, that is precisely what |gdepth| does internally. It
uses an algebra |depthAlg listDesc| and folds it over the list. One
may define an alternative |length| function as follows:

\begin{code}
length′ : ∀{A} → List A → Nat
length′ = gfold (depthAlg listDesc)
\end{code}

A depth algebra can be calculated for any description---this allows
|gdepth| to be fully generic (i.e. it works for all descriptions). One
may also define algebras for a specific type, for instance a
|countBoolsAlg| which counts the number of |true|s in a |List
Bool|. The generic |gfold| function can be used to fold this algebra.

\begin{code}
countBools : List Bool → Nat
countBools = gfold countBoolsAlg
\end{code}

We have taken a look at naturals and lists. These datatypes are
similar in their recursive structure and we want to exploit that. We
can create an ornament which can be used as a patch on the description
of naturals to get the description of lists. Descriptions do not
include names of the datatype and constructors, but they do include
names of arguments so we have to do two things to obtain lists from
naturals:

\begin{itemize}
\item The recursive argument of suc must be renamed to |"xs"|. We can
  use the expression |renameArguments 1 (just "xs" ∷ [])| to build
  such an ornament.
\item A parameter of type |Set| must be added, which must be used as an
  argument in the suc/cons constructor. The ornament to do that is
  |addParameterArg 1 "x"|.
\end{itemize}

These two ornaments have to be applied in sequence, so they are
composed using the |>>⁺| operator. The resulting ornament can be
applied to produce a new description using |ornToDesc|, and we see
that |ornToDesc nat→list| results in a description which is exactly
the same as |listDesc|:

\begin{code}
nat→list : Orn _ _ _ _ natDesc
nat→list = renameArguments 1 (just "xs" ∷ [])
  >>⁺ addParameterArg 1 "x"

test-nat→list : ornToDesc nat→list ≡ listDesc
test-nat→list = refl
\end{code}

Datatype indices can be used to \emph{refine} datatypes. Such a
refinement can ensure that values can only be built if they adhere to
a certain invariant. For instance, a length index can be added to
lists to ensure that only lists of the specified length are
allowed. One class of ornaments that inserts indices is that of
\emph{algebraic ornaments}. These use an algebra on the original
datatype to calculate the values of the indices. By folding the
algebra |depthAlg listDesc| we were able to calculate the length of a
list, but we can also use it with |algOrn| to build an ornament which
inserts a length index:

\begin{code}
list→vec : Orn _ _ _ _ listDesc
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
yet have a corresponding Agda datatype. Our descriptions are defined
in such a way that they can always be converted back to a real
datatype definition. The reflection mechanism in Agda does not yet
support the definition of datatypes, but we \emph{can} calculate the
types of every constructor and of the datatype itself. All we have to
do is write the skeleton of the datatype definition, but not the types
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

\filbreak

An essential property of ornaments is that each element of the
ornamented type can be transformed back to an element of the original
type. The generic operation |gforget| does that for a given
ornament. We can use it to define the function which transforms a
|Vec| to the corresponding |List|:

\begin{code}
vecToList : ∀{A n} → Vec A n → List A
vecToList = gforget list→vec
\end{code}

We have seen how this implementation can be used to perform generic
operations and to build and use ornaments on a high level with a
fairly limited amount of knowledge. We did not once have to look at
the actual descriptions and ornaments which are used internally. In
the rest of this thesis we will be taking a better look on how these
descriptions and ornaments have to be defined and how meta-programming
can be used to connect the descriptions to actual datatypes.
