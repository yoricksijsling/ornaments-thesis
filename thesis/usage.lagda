%include thesis.fmt

\section{Usage}\label{sec:usage}

In this section we provide a short overview of how the whole system
works. It is simply meant to show how everything fits together, so we
do not explain all the details. Later sections will expand on this.

Let us start by showing how the datatype for naturals can be quoted to
obtain a description. We use a macro (see Section \todo{ref})
|quoteDatatypeᵐ| to execute the necessary operations to convert the
|Nat| datatype into a record which contains the description. The
actual description is retrieved from the record using |desc|.

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

quotedNat = quoteDatatypeᵐ Nat

natDesc : DatDesc ε ε 2
natDesc = desc q
\end{code}

The description is of type |DatDesc ε ε 2|. The arguments of this type
indicate that this description has no parameters, no indices, and two
constructors. When a datatype does have parameters they are encoded
with a list-like structure. Looking at the |List| datatype, we see
that the single parameter of type |Set| is encoded as |ε ▷₁′ Set|:

\begin{code}
data MyList (A : Set) : Set where
  nil : MyList A
  cons : (x : A) → (xs : MyList A) → MyList A

quotedList = quoteDatatypeᵐ MyList

listD : DatDesc ε (ε ▷₁′ Set) 2
listD = desc quotedList
\end{code}

The |quotedList| record contains all the information necessary to
produce a |HasDesc| record which contains an embedding-projection pair
(see Section \todo{ref}), allowing us to convert between values of the
|List| datatype and elements of |ListDesc|. We use |deriveHasDesc| to
generate an instance of the |HasDesc| record, which is automatically
found by functions which require such an instance. One example of such
a function is |gdepth|. Once we have the |HasDesc| instance for lists
we can use |gdepth| to get the length of a list:

\begin{code}
unquoteDecl listHasDesc = deriveHasDesc listHasDesc quotedList

myLength : ∀{A} → MyList A → Nat
myLength = gdepth
\end{code}

We have taken a look at naturals and lists. These datatypes are
similar in their recursive structure and we want to exploit that. We
can create a so-called ornament (see Section \todo{ref}) which can be
used as a patch on the description of naturals to get the description
of lists. Descriptions do not include names of the datatype and
constructors, but they do include names of arguments so there are two
differences remaining:

\begin{itemize}
\item The recursive argument has been renamed from |''_''| (nothing)
  to |''xs''|. To be precise, ...
\item A parameter has been added to the datatype, which is used in ...
\end{itemize}

the only substantial difference between them is that lists carry an
extra element of type |A| in the |suc|/|cons| constructor. . We can

We can
exploit this fact by using the |addParameter| function on the
description of naturals, which gives us a so-called ornament (see
Section \todo{ref}). By applying |ornToDesc| to this ornament we get
exactly the description of lists:

\begin{code}
nat→list : Orn _ _ natDesc
nat→list = renameArguments 1 ("xs" ∷ [])
       >>⁺ addParameter 1 "x"

listDescByOrnament : DatDesc ε (ε ▷₁′ Set) 2
listDescByOrnament = ornToDesc nat→list

test-nat→list : listDescByOrnament ≡ listDesc
test-nat→list = refl

\end{code}

This description of lists |listDescByOrnament| is almost equal to the
previous |listDesc|, except for the naming of the arguments.
\begin{code}
test-nat→list : listDescByOrnament ≡ⁿ QuoteList.listDesc
test-nat→list = refl
\end{code}



Kunnen we een bestaand datatype verbinden aan een bestaande
description? Als dat mogelijk is kunnen we functies zoals forget
liften naar echte datatypes..
