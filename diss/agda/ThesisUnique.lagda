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

\begin{code}
open import Cats.Category.Base
open import Level
module _ {lo la l≈} {Cat : Category lo la l≈} where
open Category Cat

open import Data.Unit using (⊤)
\end{code}
%<*unique-def-unique>
\begin{code}
IsUniqueSuchThat : ∀ {lp A B}
  → (A ⇒ B → Set lp)
  → A ⇒ B
  → Set (la ⊔ l≈ ⊔ lp)
IsUniqueSuchThat P f = ∀ {g} → P g → f ≈ g

IsUnique : ∀ {A B} → A ⇒ B → Set (la ⊔ l≈)
IsUnique {A} {B} = IsUniqueSuchThat {A = A} {B} (λ _ → ⊤)
\end{code}
%</unique-def-unique>
%<*unique-def-exun>
\begin{code}
record ∃!′ {lp A B} (P : A ⇒ B → Set lp) : Set (la ⊔ l≈ ⊔ lp) where
  field
    arr : A ⇒ B
    prop : P arr
    unique : IsUniqueSuchThat P arr
\end{code}
%</unique-def-exun>
\begin{code}
∃!″ : ∀ {lp A B} (P : A ⇒ B → Set lp) → Set (la ⊔ l≈ ⊔ lp)
∃!″ = ∃!′

syntax ∃!′ (λ f → P) = ∃![ f ] P

syntax ∃!″ {A = A} {B} (λ f → P) = ∃![ f ∈ A ⇒ B ] P

∃! : (A B : Obj) → Set (la ⊔ l≈)
∃! A B = ∃![ f ∈ A ⇒ B ] ⊤
\end{code}

%<*unique-def-terminal>
\begin{code}
IsTerminal : Obj → Set (lo ⊔ la ⊔ l≈)
IsTerminal One = ∀ X → ∃! X One
\end{code}
%</unique-def-terminal>
\end{document}
