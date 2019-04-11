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
open import Cats.Category.Constructions.Exponential
open import Cats.Category.Constructions.Product
module _ {lo la l=} (C : Category lo la l=) {{x : HasExponentials C}}where

open Category C
open HasExponentials x hiding (curry)
open HasBinaryProducts (hasBinaryProducts)
open module Bld = Cats.Category.Constructions.Exponential.Build C using (Exp)
\end{code}
%<*types-type-curry>
\begin{code}
curry : ∀ {A B C} → A × B ⇒ C → A ⇒ B ↝ C
\end{code}
%</types-type-curry>
\begin{code}
curry {B = B} {C} f = Bld.curry (B ↝′ C) f
\end{code}
\end{document}
