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

The uniqueness principle for Products takes a slightly more interesting form.
\begin{code}
open import Cats.Category.Base
\end{code}
\begin{code}
module _ {lo la l≈} {Cat : Category lo la l≈} where
open Category Cat
open import Level
open import Cats.Category.Constructions.Unique as Unique
open Unique.Build Cat
\end{code}
%<*product-def-product>
\begin{code}
IsProduct : ∀ {li} {I : Set li} (O : I → Obj) P → (∀ i → P ⇒ O i)
  → Set (lo ⊔ la ⊔ l≈ ⊔ li)
IsProduct O P proj
  = ∀ {X} (x : ∀ i → X ⇒ O i) → ∃![ u ] (∀ i → x i ≈ proj i ∘ u)
\end{code}
  %</product-def-product>

\end{document}
