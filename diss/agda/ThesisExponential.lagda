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

open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Product as Product using (HasBinaryProducts)
open import Cats.Util.Conv

import Cats.Category.Constructions.Unique as Unique

\end{code}

\begin{code}
module _ {lo la l≈}
  (Cat : Category lo la l≈)
  {{hasBinaryProducts : HasBinaryProducts Cat}}
  where
\end{code}

\begin{code}
open Category Cat
open ≈-Reasoning
open Unique.Build Cat
open HasBinaryProducts hasBinaryProducts
\end{code}

%<*expon-exp>
\begin{code}
record Exp (B C : Obj) : Set (lo ⊔ la ⊔ l≈) where
  field
    Cᴮ : Obj
\end{code}
%</expon-exp>

%<*expon-eval>
\begin{code}
    eval : Cᴮ × B ⇒ C
\end{code}
%</expon-eval>

%<*expon-unique>
\begin{code}
    curry′ : ∀ {A} (f : A × B ⇒ C)
      → ∃![ f' ∈ A ⇒ Cᴮ ] (eval ∘ ⟨ f' × id ⟩ ≈ f)
\end{code}
%</expon-unique>

%<*expon-curry>
\begin{code}
  curry : ∀ {A} → A × B ⇒ C → A ⇒ Cᴮ
\end{code}
%</expon-curry>

\begin{code}
  curry f = curry′ f ⃗
\end{code}


\end{document}
