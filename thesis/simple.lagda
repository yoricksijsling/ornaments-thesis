%include thesis.fmt

\chapter{Ornaments on dependently typed descriptions}\label{chap:simple}

The sum-of-products descriptions of \fref{chap:sop} can be extended to
support dependent types. In the |_⊗_| constructor we used a |Set| to
indicate which type that argument has. To encode dependent types, we
want to allow this type to be determined by using a local
environment. Arguments are thus encoded as a function from the
environment |γ| to a |Set|. To maintain the old behavior, an argument
can simply ignore the environment. Which the definitions in the
upcoming sections, the description of lists becomes as follows:

\begin{code}
listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ (λ γ → A) ⊗ rec-⊗ ι ⊕ `0
\end{code}

A typical use case for dependent types is in the usage of
predicates. For instance, if the |IsLessThan7| predicate states that a
given number is lower than 7, the type |Lt7| contains a natural which
is lower than seven:

\begin{code}
IsLessThan7 : Nat → Set
IsLessThan7 n = n < 7

data Lt7 : Set where
  lt7 : (n : Nat) → IsLessThan7 n → Lt7
\end{code}

The constructor of |Lt7| uses the value of the first argument to
determine the type of the second argument. This can be encoded as a
description, where |top γ| is used to refer to the only value in the
environment |γ|.

\begin{code}
lt7Desc : DatDesc 1
lt7Desc = (λ γ → Nat) ⊗ (λ γ → IsLessThan7 (top γ)) ⊗ ι ⊕ `0
\end{code}

All the lambda-abstractions and parentheses are already obfuscating
the syntax, and this problem will become worse when we use bigger
environments and more complicated terms. McBride \cite{mcbride10}
presents a solution; SKI combinators can do the hard work of plumbing
the environment through the terms. Applicative functors are a
generalisation of SKI combinators \cite{mcbride08} and they may be
more familiar to functional programmers who are not into combinator
calculus, so we will be writing our terms in an applicative functor
style using |_<S>_| for the S combinator, |const| for the K combinator
and |_<KS>_| as a combination of |const| and |_<S>_|. With these
combinators, as defined in \fref{lst:simple-combinators}, the
following expressions are all equal:

\begin{codelst}{Combinators for terms with environments}{simple-combinators}\begin{code}
-- The S combinator
_<S>_ : ∀ {a b c} {Γ : Set a} {S : Γ → Set b} {T : (γ : Γ) → S γ → Set c} →
  (f : (γ : Γ) (s : S γ) → T γ s) → (s : (γ : Γ) → S γ) → (γ : Γ) → T γ (s γ)
f <S> s = λ γ → f γ (s γ)

_<KS>_ : ∀ {a b c} {Γ : Set a} {S : Set b} {T : S → Set c} →
  (f : (s : S) → T s) → (s : (γ : Γ) → S) → (γ : Γ) → T (s γ)
f <KS> s = const f <S> s
\end{code}\end{codelst}

\begin{code}
  fxy₁ fxy₂ fxy₃ : (γ : ⟦ Γ ⟧) → String
  fxy₁ = λ γ → f (x γ) (y γ)
  fxy₂ = const f <S> x <S> y
  fxy₃ = f <KS> x <S> y
\end{code}

The definition of |lt7Desc| can be modified to use these combinators.
The first argument did not use the environment, so we can use
|const| to always return |Nat|. In the second argument, the
pure function |IsLessThan7| is applied to a |top| which does use the
environment.

\begin{code}
lt7Desc′ : DatDesc 1
lt7Desc′ = const Nat ⊗ IsLessThan7 <KS> top ⊗ ι ⊕ `0
\end{code}

Of course, an environment can contain more than one value. The
environment is basically a stack of values, where |pop| and |top| can
be used to pick one. The behavior is like DeBruijn indices
\cite{debruijn72}: |top| means variable 0, |top ∘ pop| means variable
1, |top ∘ pop ∘ pop| means variable 2 and so forth.

In the following example we assume that a predicate |IsShorter| of
type |List A → Nat| |→ Set| exists which says that some list is shorter
than some length. A datatype |Shorter| can be defined which contains a
list, a length, and a proof that the list is shorter than that length:

\begin{code}
IsShorter : {A : Set} → List A → Nat → Set
IsShorter = ...

data Shorter (A : Set) : Set where
  shorter : (xs : List A) → (n : Nat) → IsShorter xs n → Shorter A
\end{code}

The description |shorterDesc| describes the |Shorter| datatype. In the
third argument, |top ∘ pop| is used to refer to the list and |top|
refers to the natural. With the use of the combinators |_<KS>_| and
|_<S>_| we can pretend that this is just a normal application of the
|IsShorter| predicate, but under the hood an environment is passed to
|top ∘ pop| and to |top|.

\begin{code}
shorterDesc : ∀{A} → DatDesc 1
shorterDesc {A} = const (List A) ⊗ const Nat ⊗
  IsShorter <KS> top ∘ pop <S> top ⊗ ι ⊕ `0
\end{code}

In the next section, we will start by showing how environments are
exactly implemented. Descriptions are upgraded to support the
propagation of environments in \fref{sec:simple-descriptions}. When
descriptions support dependent types, ornaments must do so as
well---they receive their upgrade in \fref{sec:simple-ornaments}.

\section{Contexts and environments}

An environment |γ| must contain a stack of values, but what is the
type of |γ|? The type has to mention the types of all the variables
and each of those types should be able to use the values of the
previous variables. For the purpose of building types of environments
we define |_▶_|, which is a left-associative version of |Σ| where
|fst| is renamed to |pop| and |snd| to |top|
(\fref{lst:simple-env}). The unit type |⊤′| can be used as the empty
environment, and it is extended with a type by using |_▶_|. In each
type, an environment |γ| containing values for all variables to the
left of it can be used. For example, if we want to write the type of
an environment containing the variables |(xs : List A)|, |(n : Nat)|
and |(p : IsShorter xs n)|, we could write it like this:

\begin{codelst}{Definition of |_▶_|}{simple-env}\begin{code}
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
\end{code}\end{codelst}

\begin{code}
ShorterEnv : {A : Set} → Set
ShorterEnv {A} = ⊤′ ▶₀ const (List A) ▶₀ const Nat ▶₀
  IsShorter <KS> top ∘ pop <S> top
\end{code}

The basic types |_▶_| and |⊤′| can contain an environment, but it is
not a very secure approach. For integration into our universe of
descriptions a universe of contexts is built. The contexts decode to
|_▶_|'s and |⊤′|'s. The definition is given in
\fref{lst:simple-cx}. This is quite a common approach to encode
contexts \cite{danielsson2007, mcbride10}. While we are at it, we also
define |_▷′_| as a shortcut when a type does not need to use the
environment. With these definitions we can create a context which, when
decoded, is equal to the |ShorterEnv| type we defined before.

\begin{codelst}{|Cx| definition and semantics}{simple-cx}\begin{code}
mutual
  data Cx : Set₁ where
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set
  ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ S
  ⟦ ε ⟧Cx = ⊤′

_▷′_ : (Γ : Cx) → Set → Cx
Γ ▷′ S = Γ ▷ const S
\end{code}\end{codelst}

\begin{code}
ShorterCx : {A : Set} → Cx₀
ShorterCx {A} = ε ▷′ List A ▷′ Nat ▷ IsShorter <KS> top ∘ pop <S> top

test-ShorterCx : ∀{A} → ⟦ ShorterCx {A} ⟧ ≡ ShorterEnv {A}
test-ShorterCx = refl
\end{code}

When we need to disambiguate between types and values in the remainder
of this thesis, we will be using the following terminology:

\begin{itemize}
\item \emph{Contexts} are usually indicated by |Γ| or |Δ|. They
\item An \emph{environment} is a specific instantiation of a context,
  containing inhabitants of the types which were indicated by the
  context. They are written as |γ| of type |⟦ Γ ⟧| or |δ| of
  type |⟦ Δ ⟧|.
\end{itemize}

\section{Descriptions}\label{sec:simple-descriptions}

For now we will be assuming that all |DatDesc|s are closed, i.e. they
do not refer to free variables. The |ConDesc|s which are directly
contained within the |DatDesc| have to be closed too, so a |DatDesc|
is essentially a list of closed |ConDesc|s. Not all |ConDesc|s have to
be closed though, because within a constructor new types are added to
the context. The context is chained through from left to right and
whenever a |_⊗_| operator is encountered, the specified type is added
to the context of the |ConDesc| which forms the tail.

In \fref{lst:simple-desc} we see how this works. The |DatDesc|
datatype specifies that each constructor starts with an empty context
|ε|. In the type of |_⊗_| we see that a |S| of type |⟦ Γ ⟧ → Set| must
be given. The value of |S| basically specifies a type which can depend
on the current context |Γ|. The context |Γ| is extended with |S|, and
this forms the context for the |ConDesc| in the tail |xs|.

\begin{codelst}{Descriptions with contexts}{simple-desc}\begin{code}
data ConDesc (Γ : Cx₁) : Set₁ where
  ι : ConDesc Γ
  _⊗_ : (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : (xs : ConDesc Γ) → ConDesc Γ

data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)
\end{code}\end{codelst}

Ideally, we would also add recursive arguments to the context, but
this is not possible with our current implementation. One would have
to extend the context in the |rec-⊗_| constructor with the fix point of
the whole description, but the whole description is not available at
during the definition of |ConDesc|.

The semantics of |ConDesc| now requires an environment before a
pattern functor can be delivered. The new semantics is given in
\fref{lst:simple-semantics}. For the |_⊗_| constructor, the
environment is applied to |S| to obtain the definitive type of that
argument. The semantics of |DatDesc| is only changed slightly to pass
the empty environment |tt| to |⟦_⟧conDesc|.

\begin{codelst}{Semantics of |ConDesc| with contexts}{simple-semantics}\begin{code}
⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ S ⊗ xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
⟦ rec-⊗ xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
\end{code}\end{codelst}

\begin{example}
We can now describe all the types from the introduction of this
chapter. To gain some insight in how the contexts are propagated and
extended we will also give a step-by-step example of how dependent
pairs (the |Σ| type) are described. We start by specifying the type,
which is parameterised by |A| and |B|, as the |Σ| type always is:

\begin{code}
pairDesc : (A : Set) (B : A → Set) → DatDesc 1
\end{code}

By using Agda's refine command, the |_⊕_| and |ε| are automatically
filled in. In the remaining hole, a closed |ConDesc| is expected.

\begin{code}
pairDesc₁ A B = ?0 ⊕ `0
-- |?0 : ConDesc ε|
\end{code}

When we add an argument of type |A| with |_⊗_|, the context of the
rest of the constructor is extended with the type |A|. Remember that
|ε ▷′ A| is defined as |ε ▷ const A|.

\begin{code}
pairDesc₂ A B = const A ⊗ ?1 ⊕ `0
-- |?1 : ConDesc (ε ▷′ A)|
\end{code}

We refine the hole with the |_⊗_| constructor and |ι| to finish the
list of arguments. Leaving us with the hole for the type of the second
argument. The required type tells us that the local context is |ε ▷′
A|. When the semantics is expanded we get the corresponding type |⊤′
▶₀ const A|, which is the type of the environment which contains the
value of the first argument.

\begin{code}
pairDesc₃ A B = const A ⊗ ?2 ⊗ ι ⊕ `0
-- |?2 : ⟦ ε ▷′ A ⟧ → Set|
-- |?2 : ⊤′ ▶₀ const A → Set|
\end{code}

Finally, we give |B <KS> top| as the implementation of the hole,
resulting in a description of dependent pairs.

\begin{code}
pairDesc A B = const A ⊗ B <KS> top ⊗ ι ⊕ `0
\end{code}

According to \fref{sec:sop-descriptions}, an isomorphism between |Σ A
B| and |μ (pairDesc A B)| should be given to be certain that this is
the right description. Doing that is honestly quite boring, so we will
just show that the definition is not \emph{entirely} wrong by giving
one half of the embedding-projection pair (one of the four functions
in the isomorphism).

\begin{code}
pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩
\end{code}
\end{example}

In the previous chapter, |conDescmap| and |datDescmap| both went from |⟦ D
⟧ X| to |⟦ D ⟧ Y|. With contexts built-in the semantics of |ConDesc|
requires an environment and the type of |conDescmap| is updated
accordingly to accomodate all contexts and all environments. The type
of |datDescmap| does not change and the implementations of both
functions still look the same. The types and definitions of |fold|
and |Alg| do not have to change either.

\begin{code}
datDescmap : ∀{#c X Y} (f : X → Y) (D : DatDesc #c) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
conDescmap : ∀{Γ X Y} (f : X → Y) (D : ConDesc Γ) →
             ∀{γ} → (v : ⟦ D ⟧ γ X) → ⟦ D ⟧ γ Y
\end{code}

\section{Ornaments}\label{sec:simple-ornaments}

Ornaments have to be upgraded to use the new contexts. Particularly,
the argument insertion ornament |_+⊗_| should be able to use the
environment to determine the type it wants to insert. One also has to
consider how the insertion or removal of arguments changes the context
of the tail. When a new argument is inserted, the rest of the ornament
should be able to make use of it.

The changing of contexts is encoded by two parameters of the |DatOrn|
datatype, a starting context |Γ| and an output context |Δ|. These
parameters tell us that the ornament goes from a |ConDesc Γ| to a
|ConDesc Δ|. To implement the ornamental algebra later on, we also
have to be able to calculate the original environment from an
environment of the ornamented type. That is, a function from |(δ : ⟦ Δ
⟧)| to |⟦ Γ ⟧| is required which we will call the \emph{environment
  transformer}. We will be working with functions between environments
a lot, so an alias |Cxf Γ Δ| is defined to mean |⟦ Γ ⟧ → ⟦ Δ ⟧|. The
environment transformer is a parameter of |ConDesc| as well. This
gives us the following types:

\begin{code}
Cxf : (Γ Δ : Cx) → Set
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧

DatOrn : ∀{#c}(D : DatDesc #c) → Set₂
ConOrn : ∀{Γ Δ} (f : Cxf Δ Γ) (D : ConDesc Γ) → Set₂
\end{code}

The environment transformer seems to go backwards here, from an
environment of the ornamented type back to an environment of the
original type. This is a result of the fact that every element of the
ornamented type has a unique corresponding element in the original
type.

We are not aware of any previous work which implemented ornaments on
datatypes with contexts like these. The treatment of them is however
very similar to how indices are treated usually in ornaments
\cite{mcbride11, dagand14-transporting}, specifically in how the
environment transformer works and is used as a parameter on the
ornament. In fact, the next chapter will show how indices can be
implemented using the same components in a very similar way.

The new definition of ornaments is given in full in
\fref{lst:simple-ornament}. An ornament is always told from the
outside what its environment transformer |c| is. This is seen in the
|_⊕_| constructor, where |id| is used as the environment transformer
for |ConOrn|. The first arguments to |_+⊗_| and |give-K| can both
depend on an environment, just like the first argument of the |_⊗_|
description. Both of them use the new environment |Δ|.

Every ornament is responsible for providing the right transformer to
its children. Ornaments like |rec-⊗_| do not change the context of the
rest of its tail and do not introduce additional changes to the
environment, so |c| is simply passed along. The |_+⊗_| ornament
extends the context with |S|, meaning that the tail ornament has to go
from context |Γ| to |Δ ▷ S|. The tail ornament must be given an
environment transformer of type |Cxf (Δ ▷ S) Γ|, while we already have
|c| of type |Cxf Δ Γ|. This transformer is given by |cxf-forget| in
\fref{lst:simple-cxf}. The other ornaments which update the context
use similar functions to produce environment transformers for their
tails.

\begin{codelst}{Ornaments with contexts}{simple-ornament}\begin{code}
data ConOrn {Γ Δ} (c : Cxf Δ Γ) : (D : ConDesc Γ) → Set₂ where
  ι : ConOrn c ι
  -⊗_ : ∀{S xs} → (xs⁺ : ConOrn (cxf-both c) xs) → ConOrn c (S ⊗ xs)
  rec-⊗_ : ∀{xs} → (xs⁺ : ConOrn c xs) → ConOrn c (rec-⊗ xs)

  _+⊗_ : ∀{xs} → (S : (δ : ⟦ Δ ⟧) → Set) →
    (xs⁺ : ConOrn (cxf-forget c S) xs) → ConOrn c xs
  rec-+⊗_ : ∀{xs} → (xs⁺ : ConOrn c xs) → ConOrn c xs

  give-K : ∀{S xs} → (s : (γ : ⟦ Δ ⟧) → S (c γ)) →
    (xs⁺ : ConOrn (cxf-inst c s) xs) → ConOrn c (S ⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} →
    (x⁺ : ConOrn id x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)
\end{code}\end{codelst}

\begin{codelst}{Environment transformers}{simple-cxf}\begin{code}
Cxf : (Γ Δ : Cx) → Set
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧

cxf-both : ∀{Γ Δ S} → (c : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ c)) (Γ ▷ S)
cxf-both c δ = c (pop δ) , top δ

cxf-forget : ∀{Γ Δ} → (c : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget c S δ = c (pop δ)

cxf-inst : ∀{Γ Δ S} → (c : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (c γ)) → Cxf Δ (Γ ▷ S)
cxf-inst c s δ = c δ , s δ
\end{code}\end{codelst}

The rest of the definitions relating to ornaments do not differ much
from the previous chapter. The interpretation function of ornaments on
constructors, |conOrnToDesc|, now works for all contexts and
environment transformers:

\begin{code}
conOrnToDesc : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} →
               ConOrn c D → ConDesc Δ
\end{code}

The implementation of |conOrnToDesc| is the same as before, except
that the environment transformer is used in the |-⊗_| ornament. When
we try to produce a description with |_⊗_|, we have to give a function
|⟦ Δ ⟧ → Set| representing a type within the ornamented context
|Δ|. The ornament stored the type within the original context: |S| of
type |⟦ Γ ⟧ → Set|. The environment transformer |(c : Cxf Δ Γ)| helps
us to transform types within the context |Γ| to types with the context
|Δ|:

\begin{code}
conOrnToDesc {c = c} (-⊗_ {S = S} xs⁺) = S ∘ c ⊗ conOrnToDesc xs⁺
\end{code}

We have seen in \fref{sec:sop-ornalgs} how the ornamental algebra for
an ornament |o| on a description |D| was built using a natural
transformation from the pattern functor of |o| to the pattern functor
of |D|. With contexts, an environment has to be provided before we get
a pattern functor for a description of a constructor, so the natural
transformation must go from the pattern functor |⟦ conOrnToDesc o ⟧ δ|
to |⟦ D ⟧ γ| for a suitable environment |γ|. By assuming that we know
the environment |δ|, we can calculate the right |γ| by applying the
environment transformer |c| to |δ|:

\begin{code}
conForgetNT : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} →
              (o : ConOrn c D) →
              ∀{δ X} → ⟦ conOrnToDesc o ⟧ δ X → ⟦ D ⟧ (c δ) X
\end{code}


\begin{example}
As a somewhat contrived example, we will define an ornament on the
|lt7Desc′| description from the introduction of this chapter. The
definition is reiterated here for convenience. The ornament inserts an
argument of type |IsOdd n| which, obviously, says that |n| must be
odd.

\begin{code}
lt7Desc′ : DatDesc 1
lt7Desc′ = const Nat ⊗ IsLessThan7 <KS> top ⊗ ι ⊕ `0

postulate
  IsOdd : Nat → Set

lt7odd : DatOrn lt7Desc′
lt7odd = -⊗ IsOdd <KS> top +⊗ -⊗ ι ⊕ `0
\end{code}

Looking at the description of the ornamented type, we can see how the
argument of |IsLessThan7| has been updated to use the second DeBruijn
index instead of the first. The call to |cxf-forget| in the type of
the |_+⊗_| constructor has caused the insertion of a |pop|.

\begin{code}
test-lt7odd : ornToDesc lt7odd ≡
  (const Nat ⊗ IsOdd <KS> top ⊗ IsLessThan7 <KS> top ∘ pop ⊗ ι ⊕ `0)
test-lt7odd = refl
\end{code}

If we postulate proofs that 3 is lower than 7 and that 3 is odd, we
can create an element of |lt7odd| for the number 3. The |forget|
function gives the expected result.

\begin{code}
postulate
  proof-that-3<7 : (3 ofType Nat) < 7
  proof-that-3-is-odd : IsOdd 3

ex-lt7odd : μ (ornToDesc lt7odd)
ex-lt7odd = ⟨ 0 , 3 , proof-that-3-is-odd , proof-that-3<7 , tt ⟩

forget-lt7odd : forget lt7odd ex-lt7odd ≡ ⟨ 0 , 3 , proof-that-3<7 , tt ⟩
forget-lt7odd = refl
\end{code}
\end{example}

% \begin{itemize}
% \item Right vs left nesting (see mcbride10: outrageous but meaningful coincidences).
% \item Compare with Σdescs: Σ can also support dependent types, but
%   with a Σ constructor the description of the tail is given as a
%   result of a function. Stuff like |countArguments| is not
%   possible. We have essentially taken the things which allow Σdescs to
%   support dependent types and moved those inside the contexts.
% \item Something about encoding |_×_| in Σ and ours?
% \end{itemize}

