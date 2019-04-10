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
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Exponential
open import Cats.Category.Constructions.Product
import Extension
import Points
\end{code}

\begin{code}
module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where
\end{code}
\begin{code}

open Category C
open HasExponentials (IsCCC.hasExponentials isCCC)
open Points.Build C
open ≈-Reasoning
open HasBinaryProducts hasBinaryProducts
open Extension.Build C {{hasBinaryProducts}}

\end{code}

%<*diagonal-type-diagonal>
\begin{code}
lawvere : {A B : Obj} → PointSurjective A (A ↝ B) → FixedPointProperty B
\end{code}
%</diagonal-type-diagonal>

%<*diagonal-pattern>
\begin{code}
lawvere record { arr = ϕ ;
                 isPointSurjective = isPointSurjective } f =
                 record { X = {!!} ; isFixedPoint = {!!} }
\end{code}
%</diagonal-pattern>

\begin{AgdaAlign}
\begin{code}
lawvere' : {A B : Obj} → PointSurjective A (A ↝ B) → FixedPointProperty B
\end{code}
\begin{code}
lawvere' record { arr = ϕ ; isPointSurjective = isPointSurjective } f =
\end{code}
%<*diagonal-h-def>
\begin{code}
  let g = (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )
\end{code}
%</diagonal-h-def>
\begin{code}
  in record { X = {!!} ; isFixedPoint = {!!} }
\end{code}
\end{AgdaAlign}

\end{document}
