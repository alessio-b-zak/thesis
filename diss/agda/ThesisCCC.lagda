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
open import Cats.Category.Constructions.Exponential using (HasExponentials)
open import Cats.Category.Constructions.Product using (HasFiniteProducts)
\end{code}

%<*ccc-def-is-ccc>
\begin{code}
record IsCCC {lo la l≈} (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈) where
  field
    hasFiniteProducts : HasFiniteProducts Cat
    hasExponentials : HasExponentials Cat
\end{code}

%</ccc-def-is-ccc>
\end{document}
