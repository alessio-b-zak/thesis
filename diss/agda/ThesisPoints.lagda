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
open import Cats.Category.Constructions.Terminal as Terminal
\end{code}

\begin{code}
module _ {lo la l=} (C : Category lo la l=) {{hasTerminal : HasTerminal C}} where

private open module C = Category C
open HasTerminal hasTerminal
\end{code}
%<*point-def-point>
\begin{code}
Point : Obj → Set la
Point X = One ⇒ X
\end{code}
%</point-def-point>

%<*point-def-fixed-point>
\begin{code}
IsFixedPoint : {B : Obj} → (f : B ⇒ B) → (s : Point B) → Set l=
IsFixedPoint f s = f ∘ s ≈ s
\end{code}
%</point-def-fixed-point>

%<*point-def-solution>
\begin{code}
IsSolution : {A B : Obj} → (f : A ⇒ B) → (a : Point A) → (b : Point B) → Set l=
IsSolution f a b = f ∘ a ≈ b
\end{code}
%</point-def-solution>

%<*point-def-has-fixed-point>
\begin{code}
record HasFixedPoint {B : Obj} (f : B ⇒ B) : Set (lo ⊔ la ⊔ l=) where
  field
    X : Point B
    isFixedPoint : IsFixedPoint f X
\end{code}
%</point-def-has-fixed-point>

%<*point-def-fixed-point-property>
\begin{code}
FixedPointProperty : Obj → Set (lo ⊔ la ⊔ l=)
FixedPointProperty B = ∀ f → HasFixedPoint {B} f
\end{code}
%</point-def-fixed-point-property>


%<*point-def-has-solution>
\begin{code}
record HasSolution {A B : Obj} (f : A ⇒ B) (b : Point B) : Set (lo ⊔ la ⊔ l=) where
  field
    X : Point A
    isSolution : IsSolution f X b
\end{code}
%</point-def-has-solution>

%<*point-def-is-point-surjective>
\begin{code}
IsPointSurjective : {A B : Obj} → (f : A ⇒ B) → Set (lo ⊔ la ⊔ l=)
IsPointSurjective f = ∀ b → HasSolution f b
\end{code}
%</point-def-is-point-surjective>

%<*point-def-point-surjective>
\begin{code}
record PointSurjective (A : Obj) (B : Obj) : Set (lo ⊔ la ⊔ l=) where
  field
    arr : (A ⇒ B)
    isPointSurjective : IsPointSurjective arr
\end{code}
%</point-def-point-surjective>

\end{document}
