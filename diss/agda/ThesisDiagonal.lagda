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
open ≈-Reasoning
⟨×⟩-resp-f : ∀ {A B D} {f g : A ⇒ B ↝ D} → f ≈ g → ⟨ f × id {B} ⟩ ≈ ⟨ g × id {B} ⟩
⟨×⟩-resp-f x = ⟨×⟩-resp x ≈.refl
\end{code}
%<*diagonal-uncurry-resp-prf>
\begin{code}
uncurry-resp : ∀ {A B D} {f g : A ⇒ B ↝ D} → f ≈ g → uncurry f ≈ uncurry g
\end{code}
%</diagonal-uncurry-resp-prf>
\begin{code}
uncurry-resp {A} {B} {D} {f} {g} x = ∘-resp-r (⟨×⟩-resp-f {A} {B} {D} {f} {g} x)
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
\end{code}
%</diagonal-pattern>
\begin{code}
  let g = (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )
      g' = (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )))
      ps = isPointSurjective g'
      u = (HasSolution.X ps)
      ϕ∘u = ( collapseToOne (uncurry (ϕ ∘ u)))
      fixedPoint = ϕ∘u ∘ u
\end{code}
%<*diagonal-fix-proof>
\begin{code}
      proof
        = begin
            f ∘ fixedPoint
          ≈⟨ {!!} ⟩
            fixedPoint
          ∎
\end{code}
%</diagonal-fix-proof>
%<*diagonal-pattern-end>
\begin{code}
      in record { X = {!!} ; isFixedPoint = {!!} }
\end{code}
%</diagonal-pattern-end>

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
%<*diagonal-g'-def>
\begin{code}
      g' = (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )))
\end{code}
%</diagonal-g'-def>
%<*diagonal-ps-def>
\begin{code}
      ps = isPointSurjective g'
      u = (HasSolution.X ps)
\end{code}
%</diagonal-ps-def>
%<*diagonal-ps-proof>
\begin{code}
      ps-proof = HasSolution.isSolution ps
\end{code}
%</diagonal-ps-proof>
%<*diagonal-isos-proof>
\begin{code}
      ϕ∘u = ( collapseToOne (uncurry (ϕ ∘ u)))
      fixedPoint = ϕ∘u ∘ u
\end{code}
%</diagonal-isos-proof>

%<*diagonal-col-unc-ps>
\begin{code}
      col-unc-ps-proof = collapseToOne-resp ( uncurry-resp ps-proof )
\end{code}
%</diagonal-col-unc-ps>

\begin{code}
      proof
        = begin
\end{code}

%<*diagonal-col-unc-ps-trans>
\begin{code}
            fixedPoint
          ≈⟨ ∘-resp-l col-unc-ps-proof ⟩
            (collapseToOne (uncurry g')) ∘ u
\end{code}
%</diagonal-col-unc-ps-trans>

\begin{code}
          ≈⟨ {!!} ⟩
            fixedPoint
          ∎
\end{code}
\begin{code}
  in record { X = fixedPoint ; isFixedPoint = {!!} }
\end{code}
\end{AgdaAlign}

\end{document}
