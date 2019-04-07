\documentclass[a4paper, 12pt]{article}
\usepackage{agda}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{autofe}

\date{}

\title{Thesis}

\begin{document}
\maketitle
In this thesis the theory of Cartesian Closure will be explored alongside the proofs of diagonalisation theorems by William Lawvere.
Here we postulate.

\begin{code}
open import Level
module ThesisCategory {lo la l≈ : Level} where
\end{code}

We begin by implementing the basic definition of a Category in Agda
\begin{code}
open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Setoid)
open import Relation.Binary.EqReasoning as EqReasoning
import Cats.Util.SetoidReasoning as SetoidR
\end{code}
%<*cat-def>
\begin{AgdaAlign}
\begin{code}
record Category lo la l≈ : Set (suc (lo ⊔ la ⊔ l≈)) where
  field
    Obj  : Set lo
    _⇒_ : Obj → Obj → Set la
\end{code}
%</cat-def>
\begin{code}[hide]
  infixr  9 _∘_
  infix   4 _≈_
  infixr  -1 _⇒_
\end{code}
%<*cat-field-comp-id>
\begin{code}
  field
    id : {O : Obj} → O ⇒ O
    _∘_  : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
\end{code}
%</cat-field-comp-id>
%<*cat-field-rel>
\begin{code}
  field
    _≈_  : ∀ {A B} → Rel (A ⇒ B) l≈
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
\end{code}
%</cat-field-rel>

%<*cat-field-comp>
\begin{code}
  field
    id-r : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    id-l : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f

    assoc : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
      → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

    ∘-resp : ∀ {A B C}
      → (_∘_ {A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

  \end{code}
\end{AgdaAlign}
%</cat-field-comp>


\end{document}
