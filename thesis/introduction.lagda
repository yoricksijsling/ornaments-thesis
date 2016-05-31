%include thesis.fmt

\chapter{Introduction}\label{chap:introduction}

Modern dependently typed languages like Agda support indices and
dependent types in their datatypes, allowing us to construct inductive
families \cite{dybjer91}. Types can contain extra information in their
indices, allowing us to place more precise restrictions on which
values our allowed in certain places. For instance, lists with a
length index are useful to build functions which require lists of
certain lengths. By adding the proper indices, we can also encode
logic of the program within a datatype. An example of this is the
addition of a type index to a datatype which encodes an expression
language; this index can be used to enforce typing rules of that
language. Building datatypes such that they precisely match the logic
of the program is an essential aspect of writing
correct-by-construction programs in functional programming languages.

This specialization of datatypes can however be a significant obstacle
to code reuse. For example; one may have defined the |List| datatype
and a function to find the lowest value in a list of naturals:

\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

lowest : List Nat → Maybe Nat
lowest [] = nothing
lowest (x ∷ xs) with lowest xs
lowest (x ∷ _) | nothing = just x
lowest (x ∷ _) | just m = just (if (lessNat x m) then x else m)
\end{code}

The |Vec| datatype is very similar; it only adds a length index:

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
\end{code}

Although we explain |Vec|s as being a |List| with an index, we
\emph{define} it as an entirely separate thing. Agda has no idea that
these two are related. If we want to get the lowest value in a |Vec|
of naturals, we have to write the whole function again:

\begin{code}
lowestᵥ : ∀{n} → Vec Nat n → Maybe Nat
lowestᵥ [] = nothing
lowestᵥ (x ∷ xs) with lowestᵥ xs
lowestᵥ (x ∷ _) | nothing = just x
lowestᵥ (x ∷ _) | just m = just (if (lessNat x m) then x else m)
\end{code}

Clearly, it might be useful if Agda actually knew about the connection
between |List|s and |Vec|s. Conor McBride \cite{mcbride11} has
presented \emph{ornaments} as a way to express relations between
datatypes. Loosely speaking, one type can be said to be an ornament of
another if it contains more information in some way, for example by
the refinement of indices or the addition of data. They can be used to
express that |Vec|s are an ornament on |List|s. |List|s themselves are
ornaments on |Nat|s, they are |Nat|s with an extra element attached to
the |suc| constructor.

....

- generics
- universes
- embedding-projection pairs

...

We make the following contributions:

\begin{enumerate}
\item We build a universe of descriptions which is used to encode
  datatypes. The descriptions support parameters, indices and
  dependent types. Contrary to many approaches, our universe must be
  conservative in the sense that only datatypes which can exist in the
  host language may be encoded in the universe. Every description
  which can be built in this system can also be converted to a real
  datatype. These descriptions are uniquely suitable for modification
  and the construction of new datatypes. The descriptions do not
  require the disabling of safety features like strict-positivity,
  type-in-type or termination checking.
\item We define ornaments for these descriptions. Due to the
  construction of our descriptions we can freely apply any ornaments
  and still be certain that the resulting description corresponds to a
  definable datatype. We have been able to translate many of the
  ornament-related concepts to our universe, including ornamental
  algebras, algebraic ornaments and reornaments. Additionally we
  define some high-level operations which can be used to modify
  descriptions without knowing anything about the implementation of
  ornaments.
\item We implement a framework which uses meta-programming to derive
  descriptions and matching embedding-projection pairs for real
  datatypes. Some operations regarding descriptions and ornaments have
  been lifted to work on real datatypes, provided that the
  embedding-projection pairs have been derived for those types. All of
  this allows for easier experimentation with ornaments.
\end{enumerate}
