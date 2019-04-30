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
\begin{code}
module ThesisRetract where

open import Level
import Cats.Category.Constructions.Iso as Iso
open import Cats.Category.Base

open import Cats.Util.Conv

import Relation.Binary.EqReasoning as EqReasoning
\end{code}

\begin{code}
module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning

\end{code}

%<*retract-def-retract>
\begin{code}
  record Retract (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      forth : A ⇒ B
      back : B ⇒ A
      forth-back : forth ∘ back ≈ id
\end{code}
%</retract-def-retract>

open Build public

\end{code}

\end{document}
