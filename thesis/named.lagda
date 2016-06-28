%include thesis.fmt

\chapter{Generic programming with descriptions}\label{chap:named}

The previous chapter defined descriptions and ornaments with all the
core features we wish to have. In this chapter, the last minor changes
are made to descriptions to make them store names of
arguments. The surrounding functionality as introduced in \cref{chap:usage}
is presented to get a true generic programming library which allows
the derivation of descriptions and embedding-projection pairs from
user-defined datatypes.

% What is quoting
One of the major goals of this thesis is to allow quoting of
datatypes. We use the term \emph{quoting} in general for the
conversion of \emph{code} to \emph{data}. More concretely, actual
definitions and terms in your Agda program may be \emph{quoted} to
representations. In the case of the quoting of datatypes, it primarily
means that a description is being calculated for a user-defined
datatype.

% Deriving
Once a datatype has been quoted, you may want to derive an
embedding-projection pair to translate between the original type and
the representation. The term 'derive' is used in the way that it is in
Haskell, where certain record instances like |Show|, |Read| and
|Generic| can be automatically derived from datatypes by the
|deriving| keyword. We will be using the |deriveHasDesc| function to
perform a similar process:

\begin{code}
deriveHasDesc : (`quotedDesc `hasDesc `dt : Name) → TC ⊤
\end{code}

% TC
The result of |deriveHasDesc| is a \emph{meta-program}, contained in
the |TC| monad. The |TC| monad is built into Agda, and meta-programs
within |TC| can be run by using keywords like |unquoteDecl|. The
meta-program can access types in the context, define new functions,
perform unification of types, normalise types, and more. Essentially,
it is a way to directly control the type-checker. A meta-program is
run during the type-checking at the exact point where it was called,
and type-checking will only continue once the result has been
computed. Type errors can occur during the execution, for instance
because one tries to unify two types which can not be unified, or
because an error is thrown manually.

% Names
The |deriveHasDesc| function requires three values of the |Name|
type. The |Name| type is also built-in, and is a reference to a
definition in the program. \emph{Every} |Name| is directly connected
to a function, datatype, record or other kind of definition. Agda
makes sure that this is always the case\footnote{Within a |TC|
  computation, new |Name|s can be created which are not necessarily
  bound to a definition. There is, however, no way for these |Name|s
  to escape the |TC| monad.}. We will be using two ways to create
|Name|s:

\begin{itemize}
\item With the |quote| keyword, a |Name| is given for an existing
  definition. So the expression |quote Vec| results in a |Name| which
  refers to the |Vec| datatype. The same notation with the |quote|
  keyword is used to \emph{show} names as well.
\item A statement like |unquoteDecl x_1 x_2 ⋯ x_n = m|. The expression
  |m| must be of type |TC ⊤|, and \emph{must} declare functions with
  the names |x_1 ⋯ x_n|. Within |m|, these names are of type
  |Name|. After the |unquoteDecl| statement |n| new definitions have
  been created.
\end{itemize}

% deriveHasDesc again
Our |deriveHasDesc| function is used in combination with the
|unquoteDecl| keyword, such that |`quotedDesc| and |`hasDesc| are
functions which must be declared by |deriveHasDesc|. The |`dt|
argument is the name of the datatype which must be quoted. This is
most easily explained with an example---Assume that the |Vec| datatype
has been defined as follows:

\begin{code}
data Vec (A : Set) : Nat → Set where
  nil : Vec A 0
  cons : ∀ n → (x : A) → (xs : Vec A n) → Vec A (suc n)
\end{code}

% Note on visibility of |n|
\begin{remark}
  The |n| argument of cons is visible, not hidden as it usually
  is. Hidden arguments are currently not supported by the
  library. This is why the constructor is named |cons| instead of
  |_∷_|.  With 3 visible arguments, the infix notation would not give
  the intended result.
\end{remark}

% Using deriveHasDesc
We use |deriveHasDesc| on the |Vec| datatype and run the meta-program
by using |unquoteDecl|. This process defines two functions for us:
|quotedVec| and |VecHasDesc|. If the name does not match a datatype,
or if the datatype can not be described by our descriptions, a type
error is thrown.

\begin{code}
-- Quote the |Vec| datatype
unquoteDecl quotedVec VecHasDesc =
  deriveHasDesc quotedVec VecHasDesc (quote Vec)

-- Two new functions have been defined:
-- |quotedVec : QuotedDesc|
-- |VecHasDesc : {A : Set} {n : Nat} → HasDesc (Vec A n)|
\end{code}

The |quotedVec| function is of type |QuotedDesc|. It contains, among
other things, the generated description and will be defined in
\cref{sec:named-quoting}. The |VecHasDesc| function returns a |HasDesc
(Vec A n)| for any |A| and |n|. The |HasDesc| record contains the
derived embedding-projection pair and is further explained in
\cref{sec:named-deriving}.

The execution of |deriveHasDesc| on a datatype |Dt| will often be
called \emph{the quoting of |Dt|}. So when we talk about 'after |Vec|
has been quoted', we mean after |deriveHasDesc| has been executed by
|unquoteDecl| like in the code above. By convention, we will always
use names like |quotedDt| and |DtHasVec| for the results of the
quoting of a specific datatype |Dt|.

\section{Descriptions and ornaments}\label{sec:named-descriptions}

When quoting datatypes, the library can see what the names of
arguments are within the constructors. A fairly small change to
descriptions allows each argument to contain such a name, of type
|String|. This is the \emph{only} change relative to the descriptions
of \cref{chap:extended}. The full definition of descriptions is given
in \cref{lst:named-desc}. The argument names have been added in front
of |_⊗_| and |rec_⊗_|, separated by a forward slash. The rest of the
definition and semantics are exactly like in
\cref{sec:ext-descriptions}. The |Vec| type can now be described in
the following way:

\begin{codelst}{Descriptions with names}{named-desc}\begin{code}
data ConDesc (I : Cx₀)(Γ : Cx₁) : Set₁ where
  ι : (o : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → ConDesc I Γ
  _/_⊗_ : (nm : String) → (S : (γ : ⟦ Γ ⟧) → Set) →
    (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
  _/rec_⊗_ : (nm : String) → (i : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) →
    (xs : ConDesc I Γ) → ConDesc I Γ
data DatDesc (I : Cx)(Γ : Cx) : (#c : Nat) → Set₁ where
  `0 : DatDesc I Γ 0
  _⊕_ : ∀{#c} → (x : ConDesc I Γ) →
    (xs : DatDesc I Γ #c) → DatDesc I Γ (suc #c)
\end{code}\end{codelst}

\begin{code}
vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = ι (const (tt , 0))
  ⊕ "n" / const Nat ⊗
    "x" / top ∘ pop ⊗
    "xs" /rec (λ γ → tt , top (pop γ)) ⊗
    ι (λ γ → tt , suc (top (pop γ)))
  ⊕ `0
\end{code}

Ornaments are changed accordingly. The copying operators |_/-⊗_| and
|_/rec_⊗_| require a name, which will overwrite the old name of the
argument. The insertion operators |_/_+⊗_| and |_/rec_+⊗_| need a name
as well for the argument being inserted. The names are the only change
compared to the ornaments in \cref{sec:ext-ornaments}. The new
definition of ornaments is in \cref{lst:named-ornament}.

\begin{codelst}{Ornaments with names}{named-ornament}\begin{code}
data Orn {I} J (u : Cxf J I)
  {Γ} Δ (c : Cxf Δ Γ) : ∀{dt}(D : Desc I Γ dt) → Set₁ where
  ι : ∀{i} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn _ u _ c (ι i)
  _/-⊗_ : ∀{nm S xs} (nm′ : String) →
    (xs⁺ : Orn _ u _ (cxf-both c) xs) → Orn _ u _ c (nm / S ⊗ xs)
  _/rec_⊗_ : ∀{nm i xs} (nm′ : String) → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (nm /rec i ⊗ xs)

  _/_+⊗_ : {xs : ConDesc I Γ} (nm : String) (S : (δ : ⟦ Δ ⟧) → Set)
    (xs⁺ : Orn _ u _ (cxf-forget c S) xs) → Orn _ u _ c xs
  _/rec_+⊗_ : {xs : ConDesc I Γ} (nm : String) (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧)
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c xs
  give-K : ∀{S xs nm} → (s : (δ : ⟦ Δ ⟧) → S (c δ)) →
    (xs⁺ : Orn _ u _ (cxf-inst c s) xs) → Orn _ u _ c (nm / S ⊗ xs)

  `0 : Orn _ u _ c `0
  _⊕_ : ∀{#c x}{xs : DatDesc I Γ #c}
    (x⁺ : Orn _ u _ c x) (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (x ⊕ xs)
\end{code}\end{codelst}

The |ornToDesc| function has been slightly updated to make sure that
the description gets the names as specified in the ornament. Some
other functions, like |forget| simply ignore the names. All the
changes required to support the new descriptions and ornaments with
names are trivial, and they will not be listed here.


\section{Quoting datatypes}\label{sec:named-quoting}

% What |QuotedDesc| contains
The quoting of a datatype gives a |DatDesc I Γ #c| for \emph{some}
|I|, |Γ| and |#c| which are not known in advance. Additionally, the
name of the datatype and a list of names of the constructors can be
read during the quoting operation, so we would like to store them as
well. The |QuotedDesc| record (\Cref{lst:named-quoteddesc}) can
contain all the information which we can extract from a datatype
definition including the indices, parameters, constructor count, names
and description.

\begin{codelst}{Quoted descriptions}{named-quoteddesc}\begin{code}
record QuotedDesc : Set₂ where
  constructor mk
  field
    {I} : Cx
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Name
    `constructorNames : Vec Name #c
    desc : DatDesc I Γ #c
\end{code}\end{codelst}


% About |Name|
The |Name| type has been used to store the names of constructors and
of the datatype. As explained in the introduction of this chapter,
this means that |`datatypeName| is connected to a real datatype, and
each of the |`constructorNames| is tied to a real
constructor\footnote{Strictly speaking, these names could be connected
  to any definition. So |`datatypeName| could just as well be the name
  of a function.}.

% Difference datatype/constructor names and argument names
One may note that datatype/constructor names and argument names are
handled very differently. Argument names are not bound to
definitions---they are always merely a |String|. It is still easy to
write a new description by hand. If the programmer does not have a
name for an argument they can always resort to writing |''_''|. If
constructor names were included in |DatDesc|, which is definitely
possible, one would not be able to write new descriptions without
needing to grab a |Name| from somewhere. A newly written description
is not bound to a real datatype, so it does not make sense to have to
connect the constructors to definitions. A |quotedDesc| \emph{is}
bound to a real datatype by the |Name|s of the datatype and
constructors.

%
The quoting of a datatype (by the use of |deriveHasDesc|) will result
in a |QuotedDesc| being defined. As an example we quote the |Vec|
datatype, just like in the introduction of this chapter. We can verify
that |(quotedVec : QuotedDesc)| is correct with a simple equality, and
we note that the datatype name and the constructor names match with
those of |Vec| and that the description contained in the |QuotedDesc|
is exactly the |vecDesc| of the previous section. The following code
will work whenever the |Vec| datatype has been defined and our library
module has been opened.

\begin{code}
unquoteDecl quotedVec VecHasDesc =
  deriveHasDesc quotedVec VecHasDesc (quote Vec)

quotedVec-check : quotedVec ≡
  mk (quote Vec) (quote Vec.nil ∷ quote Vec.cons ∷ []) vecDesc
quotedVec-check = refl
\end{code}

Alternatively, the |desc| field of the |QuotedDesc| record can be
extracted by the function |QuotedDesc.desc|:

\begin{code}
vecDesc-check : QuotedDesc.desc quotedVec ≡ vecDesc
vecDesc-check = refl
\end{code}


\section{Deriving an embedding-projection pair}\label{sec:named-deriving}

No generic programming framework is complete without having some way
to derive an embedding-projection pair for a given datatype. Looking
at the type of for instance the |vec-to| function below, we see that
it is parameterised over the parameters (|A|) and indices (|n|) of the
datatype. In a sense, what we called an embedding-projection pair is
actually a \emph{family} of embedding-projection pairs (similar to how
|Vec| is a family of types), with a family member for each combination
of parameters and indices.

\begin{code}
vec-to : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vec-from : ∀{A n} → μ vecDesc (tt , A) (tt , n) → Vec A n
\end{code}

The |HasDesc| record, as defined in \cref{lst:named-hasdesc}, can
contain one member of the family of embedding-projection pairs. It has
a type parameter |A| and the contained pair converts values between
|A| and |μ desc γ i|. The fields |desc|, |γ| and |i| together
represent a fully applied type, so the type |A| must be fully applied
as well. One could have a |HasDesc (Vec Nat 10)| or a |HasDesc (Fin
7)|, but |HasDesc Vec| is not a correct type.

\begin{codelst}{HasDesc definition}{named-hasdesc}\begin{code}
record HasDesc (A : Set) : Set₂ where
  constructor mk
  field
    {I Γ} : Cx
    {#c} : Nat
    desc : DatDesc I Γ #c
    {γ} : ⟦ Γ ⟧
    {i} : ⟦ I ⟧
    to′ : A → μ desc γ i
    from′ : μ desc γ i → A
\end{code}\end{codelst}

To fully cover the use cases of the family of embedding-projections
defined by |vec-to| and |vec-from|, one would have to define a family
of |HasDesc| records. The signature of the family of |HasDesc|s for
|Vec| is straightforward, simply parameterise by the |A| and |n|:

\begin{code}
instance
  VecHasDesc : ∀{A n} → HasDesc (Vec A n)
\end{code}

This is exactly the signature of the definition that is generated by
the quoting of |Vec|. The |instance| keyword allows the |VecHasDesc|
definition to be used for instance searching. We are effectively
treating |HasDesc| as a Haskell typeclass \cite{devriese11}, and
|VecHasDesc| provides a |HasDesc| instance for |Vec A n|. If a
function requires an instance argument |⦃ r : HasDesc B ⦄|, Agda will
consider |VecHasDesc| when trying to build a record of type |HasDesc
B|.  Of course, |VecHasDesc| will only be able to return a result of
the right type if |B| is |Vec A n| for some |A| and |n|.

Outside of the record, |HasDesc.to′| and |HasDesc.from′| are of type
|{A : Set} (r : HasDesc A) → ...|. They require a |HasDesc| record to
be passed explicitly. We expect |HasDesc| records to be defined as
instances, so we would be better off by using instance search for
these functions. The functions |to| and |from| are the versions of
|to′| and |from′| which use instance search to find the right
|HasDesc| record\footnote{The same effect could be achieved by |open
  HasDesc ⦃...⦄| with the proper qualifiers.}:

\begin{code}
to : {A : Set} ⦃r : HasDesc A⦄ →
  A → μ (HasDesc.desc r) (HasDesc.γ r) (HasDesc.i r)
to ⦃r⦄ = HasDesc.to′ r

from : {A : Set} ⦃r : HasDesc A⦄ →
  μ (HasDesc.desc r) (HasDesc.γ r) (HasDesc.i r) → A
from ⦃r⦄ = HasDesc.from′ r
\end{code}

Any time after |Vec| has
been quoted, one may use |to| or |from| for |Vec|s and the right
|HasDesc| will be found automatically. The definition
of |vec-to| and |vec-from| thus becomes trivial:

\begin{code}
vec-to : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vec-to = to
vec-from : ∀{A n} → μ vecDesc (tt , A) (tt , n) → Vec A n
vec-from = from
\end{code}


\section{Generic functions}\label{sec:named-generic}

Now that embedding-projection pairs are readily available in their
|HasDesc| instances, generic programming with actual datatypes becomes
possible. A typical example is the |fold| function. Remember the
signature of |fold| in \cref{lst:ext-fold}:

\begin{code}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X}
  (α : Alg D γ X) → μ D γ →ⁱ X
\end{code}

One may expand the |_→ⁱ_| and reorder some variables to get the
following equivalent signature:

\begin{code}
fold : ∀{I Γ #c γ i}{desc : DatDesc I Γ #c} → ∀{X} →
  (α : Alg desc γ X) → μ D γ i → X i
\end{code}

The |μ D γ i| which goes in is the generic representation of some
type. If we want to define a |gfold| which works for real types, the
|μ D γ i| must be replaced by some |A|. The |A| is required to be
representable with a description, so a |HasDesc A| is expected. This
|HasDesc| contains all the values for |I|, |Γ|, |#c|, |desc|, |γ| and
|i|---all these variables can be removed from the signature. We end up
with the following signature for |gfold|, where the notation |var _R|
is used to take the field |var| from the record |R|\footnote{In Agda,
  |var _R| can be written as |var R| \emph{if} the |HasDesc| module
  has been opened. Without opening the module one must write
  |HasDesc.var R|.}.

\begin{code}
  gfold : ∀{A}⦃ R : HasDesc A ⦄ → ∀{X} →
    Alg (desc _R) (γ _R) X → A → X (i _R)
  gfold α = fold α ∘ to
\end{code}

Now |gfold| can be used to calculate, for instance, the sum of a
|Vec|. If we assume that some algebra |vecSumAlg| exists, it can
simply be |gfold|ed over a |Vec| and the |HasDesc| record is found
automatically.

\begin{code}
vecSumAlg : Alg vecDesc (tt , Nat) (λ i → Nat)
vecSumAlg = ...

vec-example : Vec Nat 4
vec-example = cons _ 3 (cons _ 1 (cons _ 5 (cons _ 6 nil)))

vec-example-sum : gfold vecSumAlg vec-example ≡ 15
vec-example-sum = refl
\end{code}

Other functions on descriptions can be transformed to generic
functions as well, including some which work with ornaments. The
|gforget| function is a version of |forget| which works on datatypes
which have been quoted. Let us quote the |List| datatype and create a
|list→vec| ornament:

\begin{code}
unquoteDecl quotedList ListHasDesc =
  deriveHasDesc quotedList ListHasDesc (quote List)

listDesc : DatDesc ε (ε ▷₁′ Set) 2
listDesc = QuotedDesc.desc quotedList

list→vec : Orn (ε ▷′ Nat) (λ i → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι (λ δ → inv (tt , 0))
  ⊕ "n" / const Nat +⊗
     "x" /-⊗
     "xs" /rec (λ δ → inv (tt , top (pop δ))) ⊗
     ι (λ δ → inv (tt , suc (top (pop δ))))
  ⊕ `0
\end{code}

The forget function for the |list→vec| ornament goes from |μ vecDesc
(tt , A) (tt , n)| to |μ listDesc (tt , A) tt|. With the right
definition of |gforget|, |forget| can be used to transform a |Vec A n|
into a |List A|. The following works:

\begin{code}
vec-example-forget :
  gforget list→vec vec-example ≡ 3 ∷ 1 ∷ 5 ∷ 6 ∷ []
vec-example-forget = refl
\end{code}

The signature |gforget| is rather unwieldy and uncovers some problems
with the current structure of the records. This problem and how a
solution would improve the type of |gforget| is discussed in
\cref{sec:named-discussion}.


\section{Unquoting descriptions}\label{sec:named-unquoting}

The functionality defined in \cref{sec:named-quoting},
\cref{sec:named-deriving} and \cref{sec:named-generic} is similar to
what generic deriving \cite{magalhaes10} does for Haskell. A
description is calculated for a given datatype and an
embedding-projection pair is generated. Generic functions like |gfold|
and |gdepth| can be implemented. Our descriptions are carefully
engineered to \emph{always} be convertible to a real datatype, which
is what we will do in this section.

The process of generating a datatype based on a description will be
called \emph{unquoting}. Agda (version 2.5.1) does not yet support the
declaration of datatypes from the reflection mechanism, so it can not
be fully automated. We \emph{can} write the skeleton of a datatype,
and unquote the types of the constructors and of the datatype, as
Pierre-Evariste Dagand pointed out to me. So if one has a |finDesc| of
type |DatDesc (ε ▷′ Nat) ε 2| which describes the |Fin| type, the user
would at least have to write the following:

\begin{code}
data Fin : ... where
  zero : ...
  suc : ...
\end{code}

Two macros are responsible for generating the types for the ...'s:
|unquoteDat| and |unquoteCon|:

\begin{code}
macro
  unquoteDat : {I Γ #c} (D : DatDesc I Γ #c) → Tactic
  unquoteCon : {I Γ #c} (D : DatDesc I Γ #c) →
    (k : Fin #c) → (`self : Term) → Tactic
\end{code}

Macros result in a |Tactic| which is executed at the spot where the
macro is called. The tactic \emph{must} place a value in that same
spot. This means that |unquoteDat finDesc| is not of type |Tactic|,
but it is the \emph{result} of that tactic---in the case of
|unquoteDat finDesc| the result is |Set| of type |Set₁|. With these
macros the following definition of |Fin| can be built:

\begin{code}
data Fin : unquoteDat finDesc where
  zero : unquoteCon finDesc 0 Fin
  suc : unquoteCon finDesc 1 Fin
\end{code}

\begin{figure}[ht]
\centering
\includegraphics[width=\textwidth]{../img/quoting_unquoting.pdf}
\caption{The process of quoting and unquoting}
\label{fig:quoting_unquoting}
\end{figure}

Now we have the |Fin| datatype and a description |finDesc|, but no
|HasDesc| record connecting the two. There is no |QuotedDesc| record
for this datatype either. The usual quoting operation |deriveHasDesc|
can create these records, but it calculates a description as well. We
want to make use of the description that is already available, and for
this purpose |deriveHasDescExisting| has been implemented. It is
similar to |deriveHasDesc|, but takes an additional description and
will ensure that it matches with the generated description. If it does
not, an error will occur. \Cref{fig:quoting_unquoting} shows how
|deriveHasDescExisting| fits in. After the following call to
|deriveHasDescExisting|, the |quotedFin| and |FinHasDesc| functions
will be defined:

\begin{code}
unquoteDecl quotedFin FinHasDesc =
  deriveHasDescExisting quotedFin FinHasDesc
  (quote Fin) finDesc
\end{code}

We have now used a description to first unquote a datatype
semi-automatically. After that, we derived the |QuotedDesc| and
|HasDesc| records. Ideally, one would merge these operations into a
single call (it would make \cref{fig:quoting_unquoting} a lot
prettier), but that is not possible in the current version of Agda
(2.5.1). Even if the unquoting of datatypes were possible, one would
still need to give the names for all the constructors. If tactics
would support the definition of datatypes, but the existing
|unquoteDecl| would have to be used, it might look as follows:

\begin{code}
-- Speculative:
unquoteDecl quotedFin FinHasDesc Fin zero suc =
  unquoteDatatype quotedFin FinHasDesc
  finDesc Fin (zero ∷ suc ∷ [])
\end{code}

\section{Building more ornaments}\label{sec:named-moreornaments}

Writing ornaments with the |Orn| datatypes is verbose and requires a
decent understanding of how descriptions work. The ornaments do not do
a particularly good job of communicating ideas like 'add a parameter'
or 'rename these constructors'. For instance, it is not obvious at
first sight that the following ornament only renames 'x' to 'y' and
'xs' to 'ys':

\begin{code}
list-rename₁ : Orn ε id (ε ▷₁′ Set) id listDesc
list-rename₁ = ι (λ δ → inv tt)
  ⊕ "y" /-⊗
    "ys" /rec (λ δ → inv tt) ⊗
    ι (λ δ → inv tt)
  ⊕ `0
\end{code}

The |Orn| datatype provides a good low-level language which guarantees
that the ornament induces a |forget| function. For actual programming,
higher-level abstractions may be easier to work with. These
abstractions take the form of functions that generate ornaments, and
we have already seen some examples: algebraic ornaments, ornament
composition with |>>⁺| and reornamentation. In this section we give
some more examples of operations like that. We try to bring ornaments
closer to how programmers think about the relations between datatypes.

To start with, we will talk about ornaments which preserve the
\emph{structure} of the description. That is, it keeps all the |ι|'s,
|_⊗_|'s and |rec_⊗_|'s in the same place. The most obvious example of
such an ornament is the identity ornament, which does nothing. A more
general version allows changes to parameters and indices. We define it
as |reCx|:

\begin{code}
reCx : ∀{I J u Γ Δ c dt}{D : Desc I Γ dt} →
  (f : ∀ i → u ⁻¹ i) → Orn J u Δ c D
reCx {c = c} {isCon} {ι o} f = ι (f ∘ o ∘ c)
reCx {c = _} {isCon} {nm / S ⊗ xs} f = nm /-⊗ reCx f
reCx {c = c} {isCon} {nm /rec i ⊗ xs} f = nm /rec f ∘ i ∘ c ⊗ reCx f
reCx {c = _} {isDat _} {`0} f = `0
reCx {c = _} {isDat _} {x ⊕ xs} f = reCx f ⊕ reCx f
\end{code}

For every ornament, a copy ornament is created which updates the
indices and context. In the case for |ι|, an index has to be given
using an ornamented environment. We get an unornamented environment
with |c|, see what the old index is under that environment with |o|
and use |f| to convert an old index into a new index. Intuitively, the
function |f| should be seen as a function of type |⟦ I ⟧ → ⟦ J ⟧|,
with the extra requirement that |u| is the inverse of this function.

The |reCx| function can be specialised in three ways: by only allowing
updates to indices, by only allowing updates to the context/parameters
or by not allowing either. This gives the functions |reindex|,
|reparam| and |idOrn|:

\begin{code}
reindex : ∀{I J u Γ dt}{D : Desc I Γ dt} →
  (f : ∀ i → u ⁻¹ i) → Orn J u Γ id D
reindex = reCx

reparam : ∀{I Γ Δ c dt}{D : Desc I Γ dt} → Orn I id Δ c D
reparam = reCx inv

idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn I id Γ id D
idOrn = reCx inv
\end{code}

Programmers may only want to ornament one of the constructors of a
datatype. This idea is expressed by |updateConstructor|. The
programmer can specify which of the constructors to update with a |Fin
#c|, and must only give an ornament for that constructor. The identity
ornament is used for the rest of the constructors.

\begin{code}
updateConstructor : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  (k : Fin #c) → Orn I id Γ id (lookupCtor D k) →
  Orn I id Γ id D
updateConstructor {D = `0} () o
updateConstructor {D = x ⊕ xs} zero o = o ⊕ idOrn
updateConstructor {D = x ⊕ xs} (suc k) o =
  idOrn ⊕ updateConstructor k o
\end{code}

The ornament from |Nat| to |List| adds a type parameter, and then
inserts an argument of that type in the |suc| constructor. The
|addParameterArg| ornament does exactly that. The new parameter is
specified by the |(Γ ▷₁′ Set)| in the type, and |reparam| is used to
modify the whole description to work with the new context, without
really using the newly added type. After that, by using composition,
|updateConstructor| inserts one new argument in the |k|th
constructor. Because the argument is added at the start of the
constructor, the parameter can be referred to with |top|. It is
currently hard to insert the argument somewhere else in the
constructor, but it would probably be easy when the separation of
parameters discussed in \cref{sec:ext-separateparams} is implemented.

\begin{code}
addParameterArg : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  Fin #c → String → Orn I id (Γ ▷₁′ Set) pop D
addParameterArg k str = reparam
  >>⁺ updateConstructor k (str / top +⊗ reparam)
\end{code}

Another common operation when ornamenting datatypes is the renaming of
arguments. While the names do not influence the functioning of a
datatype, they will be visible when a datatype is unquoted. The
renaming of arguments in a specific constructor is done by the
|renameArguments| function. The user picks a constructor with |(k :
Fin #c)| and gives a list of |Maybe String|'s, one for each argument
in the constructor. If a |Nothing| is given for an argument, the old
name is kept. The |conRenameArguments| function is a variant which
works directly on a constructor.

\begin{code}
renameArguments : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  (k : Fin #c) →
  Vec (Maybe String) (countArguments (lookupCtor D k)) →
  Orn I id Γ id D

conRenameArguments : ∀{I Γ}{D : ConDesc I Γ} →
  Vec (Maybe String) (countArguments D) →
  Orn I id Γ id D
\end{code}

These are some examples of functions that create ornaments. Small
components like |idOrn|, |reparam|, |reindex|, |reCx|,
|renameArguments| and |updateConstructor| can be combined
easily. \Cref{chap:usage} already showed an example of what |nat→list|
could look like:

\begin{code}
nat→list′ : Orn _ _ _ _ natDesc
nat→list′ = renameArguments 1 (just "xs" ∷ [])
  >>⁺ addParameterArg 1 "x"
\end{code}

This definitely does a better job at communicating the meaning of the
changes than the low-level ornament:

\begin{code}
nat→list : Orn ε id (ε ▷₁′ Set) (λ _ → tt) natDesc
nat→list = ι (λ δ → inv tt)
  ⊕ "x" / top +⊗
    "xs" /rec (λ δ → inv tt) ⊗
    ι (λ δ → inv tt)
  ⊕ `0
\end{code}

These are two extremes, where the former is very high-level and the
later is very low-level. There is nothing wrong with something in between:

\begin{code}
nat→list″ : Orn ε id (ε ▷₁′ Set) (λ _ → tt) natDesc
nat→list″ = reparam
  ⊕ "x" / top +⊗
  (reparam >>⁺ conRenameArguments (just "xs" ∷ []))
  ⊕ `0
\end{code}


\section{Discussion}\label{sec:named-discussion}

This chapter presented the final iteration of descriptions, which is
suited to describe a fairly large class of datatypes. We showed how
datatypes can be quoted to these descriptions, and how descriptions
can be unquoted to datatypes. Some generic functions were defined,
which work on actual datatypes once their embedding-projection pairs
are derived (which is automatically done when quoting a
datatype). Finally, some higher-level ornaments were defined.

With all these components together, we hope to have made the barrier
to start working with descriptions and ornaments low enough. A user
does not necessarily need to know much about the theory to quote a
datatype, make some basic modifications, and unquote it to a new
datatype. At the very least, it is easy to figure out what the
description for a certain datatype should be by simply quoting
it. These abstractions are still leaky---if one does not write
everything just right, they will get errors which can not be
understood without a deeper understanding of these descriptions and
ornaments.

\subsection{Embedding-projection instances}\label{sec:named-ep-instances}

The |HasDesc| record is indexed by the represented type |A|, this
allows for easy instance searching \emph{by type}. When one has a
value of type |A| this works well, for instance in the use of |to|. In
the following example, the |HasDesc (Vec Nat 4)| instance is found
which contains the description, |γ| and |i|. The type of |?0| is
inferred as |μ vecDesc (tt , Nat) (tt , 4)|.

\begin{code}
vec-example-rep : ?0 -- |μ vecDesc (tt , Nat) (tt , 4)|
vec-example-rep = to vec-example
\end{code}

The other way around is not so easy. If one only knows |γ|, |i| and
the description itself, Agda can not search for a |HasDesc|
instance. This means that the type of |from vec-example-rep|, the hole
in the following example, can not be inferred. If the result type is
given by the user, or known in some other way, that can be used to
find the |HasDesc|. So the following does type check:

\begin{code}
vec-example′ : Vec Nat 4
vec-example′ = from vec-example-rep
\end{code}

While |to| and |from| seem to behave the same, this is only the case
when all the types are known. The difference is that |to| uses its
input to find the record, and |from| requires the result type before a
record can be found. One of the consequences is that the signature of
|gforget| becomes very complicated:

\begin{code}
  gforget : ∀{A}⦃ AR : HasDesc A ⦄{B}⦃ BR : HasDesc B ⦄ →
    ∀{u c} (o : Orn (I _BR) u (Γ _BR) c (desc _AR)) →
    ⦃ ieq : i _AR ≡ u (i _BR) ⦄
    ⦃ γeq : γ _AR ≡ c (γ _BR) ⦄
    ⦃ #ceq : #c _AR ≡ #c _BR ⦄
    ⦃ deq : transport (DatDesc (I _BR) (Γ _BR)) #ceq (ornToDesc o)
      ≡ desc _BR ⦄ →
    B → A
\end{code}

The ornament goes from |A| to |B|, so the forget function goes from
|B| to |A|. The |HasDesc B| instance can be searched for, which is
necessary to transform the |B| into a |μ (desc _BR) (γ _BR) (i _BR)|. By
ornamenting with |o| we get a |μ (ornToDesc o) (c (γ _BR))| |(u (i _BR))|. In
the current implementation, the result type |A| is used to find a
|HasDesc A| instance, which gives us a way to transform a |μ (desc _AR)
(γ _AR) (i _AR)| into an |A|. The types |μ (ornToDesc o) (c (γ _BR)) (u
(i _BR))| and |μ (desc _AR) (γ _AR) (i _AR)| do not line up, which is why
all the equalities are required.

A solution to this problem is to the |HasDesc| record into several
records. Time did not permit to implement this in the framework, but
\cref{lst:named-altrecords} shows how it might work. The
embedding-projection pair is in a separate record parameterised by
|A|, |desc|, |γ| and |i|. The |Embeddable| record takes over the role
of |HasDesc| and is suitable for instance search by type, while the
|Projectable| record enables searching by description. Using these
records, the |to| and |from| functions can be implemented in a way
where type information always flows from the input to the output, so
the result types of |to| and |from| can be inferred.

\begin{codelst}{Alternative embedding-projection records}{named-altrecords}\begin{code}
  record EmbeddingProjection (A : Set) {I Γ #c}
    (desc : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (i : ⟦ I ⟧) : Set₂ where
    constructor mk
    field
      to′ : A → μ desc γ i
      from′ : μ desc γ i → A

  record Embeddable (A : Set) : Set₂ where
    constructor mk
    field
      {I Γ} : Cx
      {#c} : Nat
      desc : DatDesc I Γ #c
      γ : ⟦ Γ ⟧
      i : ⟦ I ⟧
      ep : EmbeddingProjection A desc γ i

  record Projectable {I Γ #c}
    (desc : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (i : ⟦ I ⟧) : Set₂ where
    constructor mk
    field
      A : Set
      ep : EmbeddingProjection A desc γ i

  to : ∀{A}⦃ R : Embeddable A ⦄ → A → μ (desc _R) (γ _R) (i _R)
  to ⦃ mk desc γ i ep ⦄ = to′ ep

  from : ∀{I Γ #c desc γ i}⦃ R : Projectable {I} {Γ} {#c} desc γ i ⦄ →
    μ desc γ i → A _R
  from ⦃ mk A ep ⦄ = from′ ep
\end{code}\end{codelst}

The signature of the generic forget function becomes a lot
simpler. The embedding-projection pair of the result is obtained by
searching a |Projectable| with the calculated environment and indices,
so there is no need to check afterwards that the types line up.
The |ornToDesc o ≡ desc _BR| equality is still required to make sure
that the given ornament matches with the input type |B|.

\begin{code}
  gforget′ : ∀{B}⦃ BR : Embeddable B ⦄ →
    ∀{AI AΓ Adesc u c} (o : Orn {AI} (I _BR) u {AΓ} (Γ _BR) c Adesc) →
    ⦃ deq : ornToDesc o ≡ desc _BR ⦄ →
    ⦃ AR : Projectable Adesc (c (γ _BR)) (u (i _BR)) ⦄ →
    B → A _AR
\end{code}
