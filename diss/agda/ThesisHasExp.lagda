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
open import Cats.Category.Constructions.Exponential as Exponential hiding (HasExponentials)

import Cats.Category.Constructions.Unique as Unique

\end{code}


%<*hasexp-def>
\begin{code}
record HasExponentials {lo la l≈} (Cat : Category lo la l≈) : Set (lo ⊔ la ⊔ l≈)
  where
\end{code}
%</hasexp-def>

\begin{code}
  private open module Bld = Build Cat using (Exp)
  open Category Cat
  open Unique.Build Cat

\end{code}


\begin{code}
  infixr 1 _↝′_ _↝_
\end{code}
\begin{code}
  field
\end{code}

\begin{code}[hide]
    {{hasBinaryProducts}} : HasBinaryProducts Cat
\end{code}

%<*hasexp-exp>
\begin{code}
  field
    _↝′_ : ∀ B C → Exp B C
\end{code}
%</hasexp-exp>

\begin{code}
  open HasBinaryProducts hasBinaryProducts
\end{code}

%<*hasexp-expo>
\begin{code}
  _↝_ : Obj → Obj → Obj
\end{code}
%</hasexp-expo>

\begin{code}
  B ↝ C = (B ↝′ C) ᴼ
\end{code}

%<*hasexp-eval>
\begin{code}
  eval : ∀ {B C} → (B ↝ C) × B ⇒ C
\end{code}
%</hasexp-eval>

\begin{code}
  eval {B} {C} = Bld.eval (B ↝′ C)
\end{code}

%<*hasexp-curry>
\begin{code}
  curry : ∀ {A B C} → A × B ⇒ C → A ⇒ B ↝ C
\end{code}
%</hasexp-curry>

\begin{code}
  curry {B = B} {C} f = Bld.curry (B ↝′ C) f
\end{code}

%<*hasexp-uncurry>
\begin{code}
  uncurry : ∀ {A B C} → A ⇒ B ↝ C → A × B ⇒ C
\end{code}
%</hasexp-uncurry>


\begin{code}
  uncurry {B = B} {C} = Bld.uncurry (B ↝′ C)
\end{code}



\end{document}
