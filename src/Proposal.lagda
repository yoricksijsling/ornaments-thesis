%include lhs2TeX.fmt
%include polycode.fmt

\begin{code}
module Proposal where

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base

module Finite where
\end{code}

%<*foo>
\begin{code}
\end{code}
%</foo>

%<*finite-desc>
\begin{code}
  data Desc : Set where
    `0 : Desc
    `1 : Desc
    _`+_ : (A B : Desc) → Desc
    _`*_ : (A B : Desc) → Desc
\end{code}
%</finite-desc>

%<*finite-interpretation>
\begin{code}
  ⟦_⟧ : Desc → Set
  ⟦ `0 ⟧ = ⊥
  ⟦ `1 ⟧ = ⊤
  ⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A `* B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
\end{code}
%</finite-interpretation>

\begin{code}
module FiniteDependent where
  mutual
    data Desc : Set where
\end{code}
%<*finite-dep-*-desc>
\begin{code}
      _`*_ : (A : Desc)(B : ⟦ A ⟧ → Desc) → Desc
\end{code}
%</finite-dep-*-desc>

\begin{code}
    ⟦_⟧ : Desc → Set
\end{code}
%<*finite-dep-*-interpretation>
\begin{code}
    ⟦ A `* B ⟧ = Σ ⟦ A ⟧ (λ x → ⟦ B x ⟧)
\end{code}
%</finite-dep-*-interpretation>

\begin{code}
module ContextFree-Naive where
\end{code}

%<*contextfree-naive-desc>
\begin{code}
  data Desc : ℕ → Set where
    `0 : ∀{n} → Desc n
    `1 : ∀{n} → Desc n
    _`+_ : ∀{n} → (A B : Desc n) → Desc n
    _`*_ : ∀{n} → (A B : Desc n) → Desc n
    `var : ∀{n} → Fin n → Desc n
    `mu : ∀{n} → Desc (suc n) → Desc n
\end{code}
%</contextfree-naive-desc>

\begin{code}
module ContextFree-One where
\end{code}
  
\end{code}
%<*contextfree-one-base>
\begin{code}
  data Desc : Set where
    `0 : Desc
    `1 : Desc
    _`+_ : (A B : Desc) → Desc
    _`*_ : (A B : Desc) → Desc
    `var : Desc

  ⟦_⟧ : Desc → Set → Set
  ⟦_⟧ `0 X = ⊥
  ⟦_⟧ `1 X = ⊤
  ⟦_⟧ (A `+ B) X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
  ⟦_⟧ (A `* B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦_⟧ `var X = X

  data μ (D : Desc) : Set where
    ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D
\end{code}
%</contextfree-one-base>


%<*foo>
\begin{code}
\end{code}
%</foo>

