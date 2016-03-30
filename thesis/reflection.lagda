%include thesis.fmt

\subsection{Reflection in Agda}\label{sec:reflection}

Our framework is intended to be used on Agda datatypes, so we need
some way of operating on the definitions of these datatypes from
within the language itself. Agda provides us with a \emph{reflection}
framework which helps us with that.

The reflection framework includes datatypes like |Term|, |Pattern| and
|Definition| which can represent syntax trees of various parts of the
language. We give an overview of the meaning of these representations
in the next sections.

Starting with version 2.5.1, Agda provides a new way of communicating
with the type checker using the |TC| monad. Within this monad we can
make the type checker perform various operations. There are many
operations available within this monad including one which can
retrieve the types of existing definitions, one which declares a new
function and one which tries to unify two types. Agda has built in
constructs to evaluate this monad.




\subsubsection{Representation of terms}\label{sec:reflection-terms}

Within the reflection framework, terms are represented using the
|Term| datatype, shown in Listing
\ref{lst:definition-representation}. The constructors |var|, |con| and
|def| are used to refer to variables, constructors and
definitions. They take a list of arguments to which they are applied,
so we do not need a separate constructor for function
application. There are constructors for lambda-abstractions,
pattern-matching lambdas, pi-types, sorts and literals.

\begin{listing}[p]\texths
\begin{code}
postulate Name : Set

postulate Meta : Set

data Term : Set where
  var           : (x : Nat) (args : List (Arg Term)) → Term
  con           : (c : Name) (args : List (Arg Term)) → Term
  def           : (f : Name) (args : List (Arg Term)) → Term
  lam           : (v : Visibility) (t : Abs Term) → Term
  pat-lam       : (cs : List Clause) (args : List (Arg Term)) → Term
  pi            : (a : Arg Type) (b : Abs Type) → Term
  agda-sort     : (s : Sort) → Term
  lit           : (l : Literal) → Term
  meta          : (x : Meta) → List (Arg Term) → Term
  unknown       : Term

data Literal : Set where
  nat    : (n : Nat)    → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

data Sort : Set where
  set     : (t : Term) → Sort
  lit     : (n : Nat) → Sort
  unknown : Sort

Type : Set
Type = Term
 
data Visibility : Set where
  visible hidden instance′ : Visibility

data Relevance : Set where
  relevant irrelevant : Relevance

data ArgInfo : Set where
  arg-info : (v : Visibility) (r : Relevance) → ArgInfo

data Arg (A : Set) : Set where
  arg : (i : ArgInfo) (x : A) → Arg A

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x

data Abs (A : Set) : Set where
  abs : (s : String) (x : A) → Abs A
\end{code}
\caption{Datatypes for terms}\label{lst:definition-representation}
\end{listing}

The |meta| constructor represents a metavariable. In general
metavariables are unsolved variables which are introduced during the
type-checking process, but if it occurs within a |Term| it often
means that the user has written a |_| there.

|Name| is used to identify something which is defined in the
environment, and |Meta| identifies a metavariable. Both are built-in
types which come with operations to compare them or convert them to
|String|s. Local variables are not referred to by name, but by their
DeBruijn index.

Values of type |Term| can occur within the constructors of |Term| in
several ways:
\begin{itemize}
\item As a |Type|: This is defined to be the same as |Term|, so |Type
  = Term|. Within this context we will use |Term| and |Type|
  interchangeably.
\item As an |Arg Term|: When a term is used as an argument it is
  wrapped together with information about its visibility and
  relevance using an |ArgInfo| object as defined below. Writing |arg
  (arg-info visible relevant)| all the time becomes tiresome so we
  provide some pattern synonyms to relieve us of this burden.
\item As an |Abs Term|: Some terms are wrapped with a |String| which
  is the name of a variable. Within the |lam| constructor this is the
  name of the abstracted variable, and within |pi| it is the name of
  the first argument. This name is purely for cosmetics, as variables
  are referred to by their DeBruijn index.
\end{itemize}

\begin{example}
  The easiest way to obtain a |Term| is using the |quoteTerm|
  primitive. It normalizes the given expression and gives us a |Term|.

\begin{code}
quoteTerm (zero)
  ≡ lit (nat 0)
quoteTerm (3 + 3)
  ≡ lit (nat 6)
\end{code}
\end{example}

\begin{example}
  When Agda does not have all the necessary information to be able to
  properly normalize a term, it will insert metavariables where
  necessary. An example of this is in the type of the following
  function:

  \begin{code}
bad-id : (A : _) → A → A
bad-id A x = x
  \end{code}

  The user meant to allow Agda to infer the value where the underscore
  |_| was written. However, Agda responds with a warning that the
  Level of A is unknown. When we ask Agda to normalize the term |(A :
  _) → A → A| we get |(A : Set _99) → (_ : A) → A|, where |_99| is an
  unsolved metavariable. The |Term| representation of that is as
  follows:

  \begin{code}
quoteTerm ((A : _) → A → A) ≡
pi (vArg (agda-sort (set (meta _99 []))))
   (abs "A" (pi (vArg (var 0 [])) (abs "_" (var 1 []))))
  \end{code}

  We can see that the argument |A| is both visible and relevant, and
  we know that it has the type |Set _99|. The term |A → A| is wrapped
  in an |abs| which stores the name of |A|. When the |A| is referred
  to in the second argument, it has DeBruijn index 0 and within the
  term of that pi-type it has index 1.
\end{example}


\subsubsection{Representation of definitions}\label{sec:reflection-definitions}

Bare expressions are not all we can represent in the reflection
framework. The |Definition| datatype in Listing
\ref{lst:definition-datatypes} covers definitions of functions,
datatypes, records, datatype constructors, postulates and
primitives. The |function| constructor takes a list of clauses. Each
clause has a |Pattern| for each argument, and a |Term| if it is not an
absurd clause.

\begin{listing}[htb]\texths
\begin{code}
data Definition : Set where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

data Pattern : Set where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : Pattern
  var    : (s : String)  → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : Pattern

data Clause : Set where
  clause        : (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (ps : List (Arg Pattern)) → Clause
\end{code}
\caption{Datatypes for definitions}\label{lst:definition-datatypes}
\end{listing}

In the previous section we saw some uses of the |Name| type. |Name|s
are necessary to be able to refer to definitions. The ways in which a
we can get a |Name| are limited, making it hard (though not
impossible) to refer to non-existing definitions. The usual way to
obtain a name is with the |quote| keyword.

\begin{code}
name-of-Nat : Name
name-of-Nat = quote Nat
\end{code}

It is important to note that the argument for |quote| can only be a
defined name, nothing else. It can not be a variable or a term, so a
construction like |λ x → quote x| or even |quote ((λ x → x) Nat)| is
invalid.

\begin{example}
  Once we have a |Name| for a datatype we can get the |Type| and
  |Definition| for it using the |getType| and |getDefinition|
  functions. Both of these functions return a monad and we need a
  piece of machinery |evalT| to evaluate it. The proper types and
  definitions of all these functions are given in section
  \ref{sec:reflection-tc}. The type and definition of |Nat| can be
  obtained as follows:

  \begin{code}
evalT (getType (quote Nat)) ≡ agda-sort (lit 0)
evalT (getDefinition (quote Nat)) ≡
  data-type 0 (quote Nat.zero ∷ quote Nat.suc ∷ [])
  \end{code}

  This tells us that the datatype is of type |Set|, it has no parameters and two
  constructors with the names zero and suc. The names listed in the
  definition can be used to obtain further information on the
  constructors of |Nat|.
\end{example}

\begin{example}
Notably absent in the |function| constructor and |Clause| datatype are
ways to describe rewrite/with-clauses and the |where| keyword. These
constructs are not necessary because all of them can be desugared into
calls to a separate function. In the following example we see three
variants of |add2|, which all increase some number by two.

\begin{code}
add1 : Nat → Nat → Nat
add1 n 1+n = suc 1+n
add2-ext : Nat → Nat
add2-ext n = add1 n (suc n)

add2-with : Nat → Nat
add2-with n with suc n
add2-with n | 1+n = suc 1+n

add2-where : Nat → Nat
add2-where n = add1 (suc n)
  where add1 : Nat → Nat
        add1 1+n = suc 1+n
\end{code}

The |Definition| of |add2-ext| shows us the single clause where the
defined function |add1| is applied to two arguments.

\begin{code}
evalT (getDefinition (quote add2-ext)) ≡
function
(clause (vArg (var "n") ∷ [])
 (def (quote add1)
  (vArg (var 0 []) ∷
   vArg (con (quote Nat.suc) (vArg (var 0 []) ∷ [])) ∷ []))
 ∷ [])
\end{code}

The other two variants of add2 show pretty much the same |Definition|,
apart from a different name of the inner function. For example, |evalT
(getDefinition (quote| |add2-with))| contains something like |def (quote
.MyModule.with-99) (⋯)|, representing a call to a function with the
automatically generated name |.MyModule.with-99|.  The definition of
that function can be retrieved by using that |Name| directly.
\end{example}

\begin{example}
  Parameters and indices of a datatype are represented in its |Type|
  and |Definition|. Let us take a look at the datatype |Vec| with the
  usual definition:

  \begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
  \end{code}

  We can use |evalT| and |getType| to get the |Type| of |Vec| and the
  constructors |[]| and |_∷_|. The unusual
  formatting is chosen such that every line corresponds to one
  argument of the function type.

  \begin{code}
evalT (getType (quote Vec)) ≡
  pi (vArg (agda-sort (lit 0))) (abs "A" (
  pi (vArg (def (quote Nat) [])) (abs "_"
  (agda-sort (lit 0)))))
evalT (getType (quote Vec.[])) ≡ 
  pi (hArg (agda-sort (lit 0))) (abs "A" (
  def (quote Vec) (vArg (var 0 []) ∷ vArg (lit (nat 0)) ∷ [])))
evalT (getType (quote Vec._∷_)) ≡
  pi (hArg (agda-sort (lit 0))) (abs "A" (
  pi (hArg (def (quote Nat) [])) (abs "n" (
  pi (vArg (var 1 [])) (abs "_" (
  pi (vArg (def (quote Vec) (vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))) (abs "_" (
  def (quote Vec) (vArg (var 3 []) ∷
       vArg (con (quote Nat.suc) (vArg (var 2 []) ∷ [])) ∷ [])))))))))
  \end{code}

  These types are what you would expect them to be given the
  definition, with a slight addition; Every constructor includes the
  parameter |{A : Set}| as a hidden argument. The indices do not get any
  special treatment. The |Definition| which we get using
  |getDefinition| also tells us that the number of parameters is one,
  allowing us to differentiate between parameters and indices.

  \begin{remark}
    We are taking some liberty with these equalities.  The |0| in the
    constructor for |[]| only becomes |lit (nat 0)| after a
    normalisation step which we do not show. In the current version of
    Agda, |0| is internally translated to |fromNat 0|, which shows up
    in the type of |[]|.
  \end{remark}
\end{example}


\subsubsection{The TC monad}\label{sec:reflection-tc}

Within TC monad one can write meta-programs which can interact with
the underlying type-checking mechanics. These meta-programs - or TC
computations - are evaluated once the compiler passes the source
location where they are invoked. Within such a meta-program the user
can access reflected terms and types of values within the environment
in the context and perform various operations on them. During the
evaluation of these operations the proper type-checking is performed
and type errors may occur.

This system has been in place since Agda version 2.5.1 and is based on
the work on elaborator reflection \todo{ref thesis Christiansen} in
Idris. The core idea is the same, though many of the actual operations
are different. For completeness, the full list of TC operations is in
figure \ref{lst:TC-operations} but we will not explain nor use all of
them. The list also contains the already familiar functions |getType|
and |getDefinition|. These do not have an effect themselves, but their
results are influenced by other operations in the monad. To maintain
the right order of operations they must also return a TC computation.
\todo{Differences in particular: Idris elaborator has a rotating list
  of unsolved holes which can be filled or skipped. Agda has
  metavariables which can occur anywhere, and they are solved by
  unification.}

\begin{listing}[htb]\texths
\begin{code}
data ErrorPart : Set where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  nameErr : Name → ErrorPart

postulate
  TC             : ∀ {a} → Set a → Set a
  returnTC       : ∀ {a} {A : Set a} → A → TC A
  bindTC         : ∀ {a b} {A : Set a} {B : Set b} →                  
                   TC A → (A → TC B) → TC B
  unify          : Term → Term → TC ⊤
  typeError      : ∀ {a} {A : Set a} → List ErrorPart → TC A
  inferType      : Term → TC Type
  checkType      : Term → Type → TC Term
  normalise      : Term → TC Term
  catchTC        : ∀ {a} {A : Set a} → TC A → TC A → TC A
  quoteTC        : ∀ {a} {A : Set a} → A → TC Term
  unquoteTC      : ∀ {a} {A : Set a} → Term → TC A
  getContext     : TC (List (Arg Type))
  extendContext  : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
  inContext      : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A
  freshName      : String → TC Name
  declareDef     : Arg Name → Type → TC ⊤
  defineFun      : Name → List Clause → TC ⊤
  getType        : Name → TC Type
  getDefinition  : Name → TC Definition
  blockOnMeta    : ∀ {a} {A : Set a} → Meta → TC A
\end{code}
\caption{Operations in the TC monad}\label{lst:TC-operations}
\end{listing}

In the previous section we used |evalT| to evaluate a TC computation,
but this is not built-in to Agda. Before seeing how |evalT| is
implemented we have to study the ways in which Agda does allow us to
use the TC monad. We will give a short explanation of the three
keywords relevant for this purpose, and provide examples later.

\begin{itemize}
  \item |unquote e| expects an |e| of type |Term → TC ⊤|. This is
    usually called a |Tactic|.
\begin{code}
Tactic : Set
Tactic = (hole : Term) → TC ⊤
\end{code}
    An |unquote e| is used as an expression which has the value of the
    hole. Which means that the |(hole : Term)| which is passed in has
    the type which is enforced by the context and can be used to
    return a value by unifying another |Term| with it. This is further
    explained in the examples below.
  \item |unquoteDecl x₁ x₂ ⋯ xn = m| is used to declare and define
    functions. Multiple functions can be defined at the same time.
    |x₁| to |xn| are the names these new functions will have. |m| is
    the TC computation of type |TC ⊤| and it must define the functions
    |x₁ ⋯ xn| using |declareDef| and |defineFun|. |x₁ ⋯ xn| are of
    type |Name| within |m|, but after |unquoteDecl| they have the
    types as defined by |declareDef|.
  \item |unquoteDef x₁ x₂ ⋯ xn = m| is the same as |unquoteDecl|, but
    the names |x₁ ⋯ xn| have to be declared in advance.
\end{itemize}

\begin{example}
  To get a better understanding of the |hole| argument, we can use
  |typeError| to throw an error which shows the value of |hole|. The
  hole is just a metavariable, so compiling the following definition
  results in an error with a message similar to |_99|.

  \begin{code}
throw-hole-term : Bool
throw-hole-term = unquote (λ hole → typeError (termErr hole ∷ []))
  \end{code}

  Do note that the |_99| in that error message is just the string
  representation of the |Term| which is actually being thrown. To show
  what the |Term| looks like we quote it using |quoteTC : A → TC
  Term|. This creates a |Term| representation of the |Term|
  representation of the hole. Compilation of the following definition
  throws an error with a message like |meta _99 []|.

  \begin{code}
throw-hole-term' : Bool
throw-hole-term' = unquote (λ hole → quoteTC hole >>= λ `hole →
                   typeError (termErr `hole ∷ []))
  \end{code}

  Even though the hole is just a meta-variable, we do have information
  about its type. The term is unknown at the time but the type is
  not. We can obtain the type information with |inferType: Term → TC
  Type|. This definition throws an error with the message |Bool|:

  \begin{code}
throw-hole-type : Bool
throw-hole-type = unquote (λ hole → inferType hole >>= λ x →
                  typeError (termErr x ∷ []))
  \end{code}
  \vskip-2em
\end{example}

\begin{example}
  A common pattern in |Tactic|s is to fill the hole with some
  |Term|\footnote{In older versions of Agda, filling the hole was the
    only behaviour of |unquote|.}. We use |unify : Term → Term → TC ⊤|
  to unify a chosen value with the hole. The metavariable in the hole
  is then solved to be equal to our chosen value. We can write a
  tactic |fill-7-tactic| which fills a hole with the natural number 7,
  such that |unquote fill-7-tactic ≡ 7|:

  \begin{code}
fill-7-tactic : Tactic
fill-7-tactic hole = unify (lit (nat 7)) hole
  \end{code}
  \vskip-2em
\end{example}

\begin{example}
  Say we have a function which returns a value within the |TC|
  monad. For example the number of constructors in a datatype:

  \begin{code}
countConstructors : Name → TC Nat
  \end{code}

  To extract the |Nat| from the monad we need some way of evaluating
  it. We can define a function |evalTC : TC A → Tactic| which
  evaluates a |TC| computation with a return value of type |A|, and
  gives back that return value in the hole. It has the interesting
  property that |unquote (evalTC (return x)) ≡ x|. We can easily
  extract the value |v| within the monad, but it has to be quoted
  before we can unify it with the hole. Additionally, we expect
  |unquote (evalTC t) : A| when |t : TC A| so we say that |hole| must
  be of type |A| using |checkType|. Without |checkType| there are some
  edge cases where type information is lost when the type is not
  inferable from the term.

  \begin{code}
evalTC : ∀ {a} {A : Set a} → TC A → Tactic
evalTC {A = A} c hole =
  do v ← c
  =| `v ← quoteTC v
  -| `A ← quoteTC A
  -| checkedHole ← checkType hole `A
  -| unify checkedHole `v
  \end{code}

  With |evalTC| we can use the |countConstructors| function quite
  easily: |unquote| |(evalTC| |(countConstructors (quote Nat))) ≡
  2|. There is still some syntactical overhead here, which we will get
  rid of in the next section.
\end{example}

\todo{unquotedecl example?}

\subsubsection{Macros}\label{sec:reflection-macros}

Macros provide some syntactical sugar for |Tactic|s. |Tactic|s often
take arguments which have to be quoted first and to use them they are
wrapped in an |unquote|. The number of |quote|s |quoteTerm|s and
|unquote|s can be reduced by defining a |Tactic| within a macro
block. When a macro is applied, |quoteTerm| is applied to arguments of
type |Term| and |quote| is applied to arguments of type |Name|. The
whole macro application is |unquoted|.

\begin{example}
  The example using |evalTC| and |countConstructors| can be improved
  upon using macros. The macro application |countConstructorsᵐ Nat|
  desugars to |unquote| |(countConstructorsᵐ (quote Nat))|, so we get
  that |countConstructorsᵐ Nat ≡ 2|.

  \begin{code}
macro
  countConstructorsᵐ : Name → Tactic
  countConstructorsᵐ n = evalTC (countConstructors n)
  \end{code}
  \vskip-2em
\end{example}

\begin{example}
  The |evalTC| function is a |Tactic| and can be wrapped in a
  macro. As promised, we finally define the |evalT| macro which we
  used in section \ref{sec:reflection-definitions}.

  \begin{code}
macro
  evalT : ∀ {a} {A : Set a} → TC A → Tactic
  evalT = evalTC
  \end{code}

  With the |evalT| macro we can replace all occurences of |unquote
  (evalTC t)| with |evalT t|, so |unquote| |(evalTC (countConstructors
  (quote Nat)))| will become |evalT| |(countConstructors| |(quote
  Nat))|. This is not that useful, so in practice we are better off by
  defining separate macros for specific functions as we did in the
  previous example.
\end{example}

\todo{conclusion?}
