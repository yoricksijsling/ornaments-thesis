%include thesis.fmt

\chapter{Ornaments on dependently typed descriptions}\label{chap:simple}

The sum-of-products descriptions of \cref{chap:sop} can be extended to
support dependent types. In the |_⊗_| constructor we used a |Set| to
indicate which type that argument has. To encode dependent types, we
want to allow this type to depend on values and types in the
context. Let us first establish some terminology:

\begin{itemize}
\item The term \emph{context} will be used to indicate what variables
  are available and which types they have. Within the |List| datatype
  for example (as defined in \cref{chap:usage}), the context consists
  of at least the type parameter |A| of type |Set|. In the second
  argument of the |cons| constructor, the variable |x| of type |A| is
  also in the context, though it is not used. If cons had more
  arguments after that, |(xs : List A)| would be in the context as
  well. In this thesis, contexts are usually indicated by a |Γ|, with
  |Δ| as an alternative. Contexts have the type |Cx|, and are defined
  in \cref{sec:simple-contexts}.
\item An \emph{environment} is a specific instantiation of a context,
  containing inhabitants of the types which were indicated by the
  context. Environments are written as |γ| of type |⟦ Γ ⟧| or |δ| of
  type |⟦ Δ ⟧|. The meaning of their types is explained in
  \cref{sec:simple-contexts} as well.
\end{itemize}

In a description, the types of arguments were specified with a
|Set|. Arguments with dependent types are encoded as a function from
an environment |(γ : ⟦ Γ ⟧)| to a |Set| is used. To maintain the old
behavior, an argument can simply ignore the environment. With the
definitions in the upcoming sections, the description of lists will
be written as follows:

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

More often than not, we will be writing the arguments in point-free
style if we can. In the definition of |lt7Desc|, the functions |const|
and |_∘_| can be used to get rid of a lot of parentheses.

\begin{code}
lt7Desc′ : DatDesc 1
lt7Desc′ = const Nat ⊗ IsLessThan7 ∘ top ⊗ ι ⊕ `0
\end{code}

Of course, an environment can contain more than one value. The
environment is basically a stack of values (more precisely, a
snoc-list), where |pop| and |top| can be used to refer to a value in
the context, in the style of DeBruijn indices \cite{debruijn72}. So
|top γ| means variable 0, |top (pop γ)| means variable 1, |top (pop
(pop γ))| means variable 2 and so forth.

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
third argument of the constructor, |top (pop γ)| is used to refer to
the list and |top γ| refers to the natural.

\begin{code}
shorterDesc : ∀{A} → DatDesc 1
shorterDesc {A} = const (List A) ⊗ const Nat ⊗
  (λ γ → IsShorter (top (pop γ)) (top γ)) ⊗ ι ⊕ `0
\end{code}

Note that the third argument of the constructor can not be written
point-free with just |_∘_| and |const|. It \emph{is} possible with an
S-combinator, as McBride \cite{mcbride10} demonstrates. Applicative
functors are a generalisation of SKI combinators \cite{mcbride08}, so
one might even choose to write that argument of |shorterDesc| in
applicative style as |IsShorter <KS> top ∘| |pop <S> top|. While that
style works well for expressions like these, it quickly breaks down
for more complicated ones.

In the next section, we will start by showing how environments are
exactly implemented. Descriptions will be revised to support the
propagation of environments in \cref{sec:simple-descriptions}. When
descriptions support dependent types, ornaments must do so as
well---they will be revised in \cref{sec:simple-ornaments}.

\section{Contexts and environments}\label{sec:simple-contexts}

An environment |γ| must contain a stack of values, but what is the
type of |γ|? The type has to mention the types of all the variables
and each of those types should be able to use the values of the
previous variables. For the purpose of building types of environments
we define |_▶_|, which is a left-associative version of |Σ| where
|fst| is renamed to |pop| and |snd| to |top|
(\Cref{lst:simple-env}). The unit type |⊤′| can be used as the empty
environment, and types are added to the right of it by using |_▶_|. In
each type, an environment |γ| containing values for all variables to
the left of it can be used. For example, if we want to write the type
of an environment containing the variables |(xs : List A)|, |(n :
Nat)| and |(p : IsShorter xs n)|, we could write it like this:

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
  (λ γ → IsShorter (top (pop γ)) (top γ))
\end{code}

The basic types |_▶_| and |⊤′| can contain an environment, but they
can not be used for pattern matching. There is no way to inspect a
value of type |Set| to see if it is a |_▶_| or |⊤′|. For this purpose
a universe of contexts |Cx| is built. The |Cx| decodes to |_▶_|'s and
|⊤′|'s. The definition is given in \cref{lst:simple-cx}. This is quite
a common approach to encode contexts \cite{danielsson07,
  mcbride10}. While we are at it, we also define |_▷′_| as a shortcut
when a type does not need to use the environment. With these
definitions we can create a context which, when decoded, is equal to
the |ShorterEnv| type we defined before.

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
ShorterCx {A} = ε ▷′ List A ▷′ Nat ▷ (λ γ → IsShorter (top (pop γ)) (top γ))

test-ShorterCx : ∀{A} → ⟦ ShorterCx {A} ⟧ ≡ ShorterEnv {A}
test-ShorterCx = refl
\end{code}

\section{Descriptions}\label{sec:simple-descriptions}

For now we will be assuming that all |DatDesc|s are closed, i.e. they
do not refer to free variables. The |ConDesc|s which are directly
contained within the |DatDesc| have to be closed too, so a |DatDesc|
is essentially a list of closed |ConDesc|s. Not all |ConDesc|s have to
be closed though, because within a constructor new types are added to
the context. The context is chained through from left to right and
whenever a |_⊗_| operator is encountered, the specified type is added
to the context of the |ConDesc| which forms the tail.

In \cref{lst:simple-desc} we see how this works. The |DatDesc|
datatype specifies that each constructor starts with an empty context
|ε|. In the type of |_⊗_| we see that a |S| of type |⟦ Γ ⟧ → Set| must
be given. The value of |S| specifies a type which can depend on the
current context |Γ|. The context |Γ| is extended with |S|, and this
forms the context for the |ConDesc| in the remainder of the ornament |xs|.

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
this is fundamentally impossible with our current implementation. This
problem will be discussed in \cref{sec:discussion-ri}.

The semantics of |ConDesc| now requires an environment before a
pattern functor can be delivered. The new semantics is given in
\cref{lst:simple-semantics}. For the |_⊗_| constructor, the
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

Finally, we give |B ∘ top| as the implementation of the hole,
resulting in a description of dependent pairs.

\begin{code}
pairDesc A B = const A ⊗ B ∘ top ⊗ ι ⊕ `0
\end{code}

According to \cref{sec:sop-descriptions}, an isomorphism between |Σ A
B| and |μ (pairDesc A B)| should be given to be certain that this is
the right description. Doing that is straightforward, so we will only
show that the definition is not \emph{entirely} wrong by giving one
half of the embedding-projection pair (one of the four functions in
the isomorphism).

\begin{code}
pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩
\end{code}
\end{example}

In the previous chapter, |conDescmap| and |datDescmap|
(\Cref{lst:sop-map}) were defined as the functorial map on the
semantics of descriptions. For a given description |D| and a function
from |X| to |Y|, they turned a |⟦ D ⟧ X| into a |⟦ D ⟧ Y|. With
contexts built-in, the semantics of |ConDesc| requires an environment
and the type of |conDescmap| is updated accordingly to accomodate all
contexts and all environments. The type of |datDescmap| does not
change and the implementations of both functions still look the
same.

\begin{code}
datDescmap : ∀{#c X Y} (f : X → Y) (D : DatDesc #c) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
conDescmap : ∀{Γ X Y} (f : X → Y) (D : ConDesc Γ) →
             ∀{γ} → (v : ⟦ D ⟧ γ X) → ⟦ D ⟧ γ Y
\end{code}

The types and definitions of |fold| and |Alg| do not change at all,
though they do make use of the new |conDescmap| through |datDescmap|.

\begin{code}
Alg : ∀{#c} → DatDesc #c → Set → Set
Alg D X = ⟦ D ⟧ X → X

fold : ∀{#c}{D : DatDesc #c}{X} (α : Alg D X) → μ D → X
fold {D = D} α ⟨ xs ⟩ = α (datDescmap (fold α) D xs)
\end{code}

\section{Ornaments}\label{sec:simple-ornaments}

Ornaments have to be revised to use the new contexts. Particularly,
the argument insertion ornament |_+⊗_| should be able to use the
environment to determine the type it wants to insert. One also has to
consider how the insertion or removal of arguments changes the context
of the remainder of the constructor. When a new argument is inserted,
the rest of the ornament should be able to use it.

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
\cref{lst:simple-ornament}. An ornament is always told from the
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
\cref{lst:simple-cxf}. The other ornaments which update the context
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
environment transformers. It used to go from |ConOrn D| to |ConDesc|,
now the signature becomes:

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

We have seen in \cref{sec:sop-ornalgs} how the ornamental algebra for
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
lt7Desc′ = const Nat ⊗ IsLessThan7 ∘ top ⊗ ι ⊕ `0

postulate
  IsOdd : Nat → Set

lt7odd : DatOrn lt7Desc′
lt7odd = -⊗ IsOdd ∘ top +⊗ -⊗ ι ⊕ `0
\end{code}

Looking at the description of the ornamented type, we can see how the
argument of |IsLessThan7| has been updated to use the second DeBruijn
index instead of the first. The call to |cxf-forget| in the type of
the |_+⊗_| constructor has caused the insertion of a |pop|.

\begin{code}
test-lt7odd : ornToDesc lt7odd ≡
  (const Nat ⊗ IsOdd ∘ top ⊗ IsLessThan7 ∘ top ∘ pop ⊗ ι ⊕ `0)
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

