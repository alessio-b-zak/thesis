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
open import Level
import Cats.Category.Constructions.Iso as Iso
open import Cats.Category.Base
open import Diagonal renaming (diagonal to lawvere)
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Exponential
open import Cats.Util.Conv
import Points
import Retract

import Relation.Binary.EqReasoning as EqReasoning
\end{code}

\begin{code}
module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC)
  open Iso.Build C
  open ≈-Reasoning
  open Points.Build C

  open Retract.Build C

\end{code}

%<*Y-def-corollary>
\begin{code}
  corollary : {X : Obj} → Retract X (X ↝ X) → FixedPointProperty X
\end{code}
%</Y-def-corollary>

%<*Y-def-corollary-body>
\begin{code}
  corollary {X} record { forth = forth ; back = back ; forth-back = forth-back }
    = lawvere C {X} (record { arr = forth ; isPointSurjective = λ b → {!!} })
\end{code}
%</Y-def-corollary-body>


\begin{code}

  corollary' : {X : Obj} → Retract X (X ↝ X) → FixedPointProperty X
  corollary' {X} record { forth = forth ; back = back ; forth-back = forth-back }
    = lawvere C {X} (record { arr = forth ;
      isPointSurjective = λ b →
\end{code}

%<*Y-point-surjective>
\begin{code}
       record { X = back ∘ b ; isSolution = begin
                                               forth ∘ (back ∘ b)
                                             ≈⟨ unassoc ⟩
                                               (forth ∘ back) ∘ b
                                             ≈⟨ ∘-resp-l forth-back ⟩
                                               id ∘ b
                                             ≈⟨ id-l ⟩
                                               b
                                             ∎ } })
\end{code}
%</Y-point-surjective>

\end{document}
