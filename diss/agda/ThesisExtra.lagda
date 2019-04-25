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
module ThesisExtra where

open import Level
import Cats.Category.Constructions.Iso as Iso
open import Cats.Category.Base
open import Diagonal renaming (diagonal to lawvere)
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Exponential
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Product
open import Data.Product hiding (uncurry ; curry)
open import Cats.Util.Conv
open import Extension
import Points
import Retract

import Relation.Binary.EqReasoning as EqReasoning

module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC)
  open HasTerminal (HasFiniteProducts.hasTerminal (IsCCC.hasFiniteProducts isCCC))
  open HasBinaryProducts (HasExponentials.hasBinaryProducts (IsCCC.hasExponentials isCCC))
  open Iso.Build C
  open ≈-Reasoning
  open Points.Build C
  open Extension.Build C

  module _ {X : Obj} {ps : PointSurjective X (X ↝ X)} where

    open module PS = PointSurjective ps
\end{code}

%<*extra-applicative-op>
\begin{code}
    _⋆_ : (A : Point X) → (B : Point X) → (Point X)
    a ⋆ b = eval ∘ ⟨ PS.arr × id ⟩ ∘ (⟨ a , b ⟩)
\end{code}
%</extra-applicative-op>

%<*extra-ffpt>
\begin{code}
    first-fixed-point-theorem : (f : Point X) → Σ (Point X) (λ x → f ⋆ x ≈ x)
\end{code}
%</extra-ffpt>

%<*extra-x-def>
\begin{code}
    first-fixed-point-theorem f
      = let x = (PS.arr) ∘ f
\end{code}
%</extra-x-def>

%<*extra-x-isos>
\begin{code}
            y = collapseToOne (uncurry (x))
\end{code}
%</extra-x-isos>

%<*extra-x-law>
\begin{code}
            z = lawvere C ps y
\end{code}
%</extra-x-law>

%<*extra-x-fix>
\begin{code}
            fixedPoint = HasFixedPoint.X z
            fixedPointProof = HasFixedPoint.isFixedPoint z
\end{code}
%</extra-x-fix>

%<*extra-fix-proof>
\begin{code}
            proof = begin
                      f ⋆ fixedPoint
                    ≈⟨ {!!} ⟩
                      fixedPoint
                    ∎
\end{code}
%</extra-fix-proof>

\begin{code}
                            in {!!}
\end{code}


\begin{code}
    fixed-point-theorem' : (f : Point X) → Σ (Point X) (λ x → f ⋆ x ≈ x)
    fixed-point-theorem' f
      = let x = (PS.arr) ∘ f
            y = collapseToOne (uncurry x)
            z = lawvere C ps y
            fixedPoint = HasFixedPoint.X z
            fixedPointProof = HasFixedPoint.isFixedPoint z
\end{code}

\begin{code}
            proof = begin
\end{code}

%<*extra-expand-pre>
\begin{code}
                      f ⋆ fixedPoint
\end{code}
%</extra-expand-pre>

%<*extra-expand>
\begin{code}
                    ≈⟨ ≈.refl ⟩
                      eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ f , fixedPoint ⟩
\end{code}
%</extra-expand>

\begin{code}
                    ≈⟨ {!!} ⟩
                      fixedPoint
                    ∎
\end{code}

\begin{code}
         in {!!}
\end{code}
\end{document}
