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
open import Data.Bool
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


%<*product-def-prod>
\begin{code}
record Product {li} {I : Set li} (O : I → Obj) : Set (lo ⊔ la ⊔ l≈ ⊔ li) where
  field
    prod : Obj
    proj : ∀ i → prod ⇒ O i
    isProduct : IsProduct O prod proj
\end{code}
%</product-def-prod>


%<*product-def-bool>
\begin{code}
Bool-elim : ∀ {a} {A : Bool → Set a} → A true → A false → (i : Bool) → A i
Bool-elim x y true = x
Bool-elim x y false = y
\end{code}
%</product-def-bool>

%<*product-def-binprod>
\begin{code}
BinaryProduct : Obj → Obj → Set (lo ⊔ la ⊔ l≈)
BinaryProduct A B = Product (Bool-elim A B)
\end{code}
%</product-def-binprod>


\end{document}
