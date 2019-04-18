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
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary using (¬_)
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
open Extension.Build C {{hasBinaryProducts}} hiding (δ)
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


%<*diagonal-delta>
\begin{code}
δ : {A : Obj} → A ⇒ A × A
δ = ⟨ id , id ⟩
\end{code}
%</diagonal-delta>

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
            fixedPoint
          ≈⟨ {!!} ⟩
            f ∘ fixedPoint
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
\end{code}
%</diagonal-col-unc-ps-trans>

%<*diagonal-col-unc-ps-trans2>
\begin{code}
            (collapseToOne (uncurry g')) ∘ u
\end{code}
%</diagonal-col-unc-ps-trans2>

%<*diagonal-g'-reduc>
\begin{code}
          ≈⟨ ∘-resp-l (∘-resp-l uncurry∘curry) ⟩
            (collapseToOne (extendToOne ( f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ))) ∘ u
          ≈⟨ ∘-resp-l (collapseExtendIso) ⟩
\end{code}
%</diagonal-g'-reduc>

%<*diagonal-g'-reduc1>
\begin{code}
            (f ∘ (eval ∘ (⟨ ϕ × id ⟩ ∘ δ))) ∘ u
\end{code}
%</diagonal-g'-reduc1>

%<*diagonal-reassoc>
\begin{code}
          ≈⟨ ∘-resp-l unassoc ⟩
            ((f ∘ eval) ∘ ((⟨ ϕ × id ⟩) ∘ δ)) ∘ u
          ≈⟨ ∘-resp-l unassoc ⟩
            (((f ∘ eval) ∘ (⟨ ϕ × id ⟩)) ∘ δ) ∘ u
          ≈⟨ ∘-resp-l (∘-resp-l assoc) ⟩
            ( (f ∘ (eval ∘ ⟨ ϕ × id ⟩)) ∘ δ) ∘ u
          ≈⟨ assoc ⟩
\end{code}
%</diagonal-reassoc>

%<*diagonal-reassoc1>
\begin{code}
            ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (δ ∘ u)
\end{code}
%</diagonal-reassoc1>

%<*diagonal-in-u>
\begin{code}
          ≈⟨ ≈.refl ⟩
            ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ ⟨ id , id ⟩ ∘ u
          ≈⟨ ∘-resp-r ⟨,⟩-∘ ⟩
            ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (⟨ (id ∘ u) , (id ∘ u) ⟩)
          ≈⟨ ∘-resp-r (⟨,⟩-resp id-l id-l) ⟩
            ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ ⟨ u , u ⟩
          ≈⟨ ∘-resp-l unassoc ⟩
            ((f ∘ eval) ∘ ⟨ ϕ × id ⟩) ∘ ⟨ u , u ⟩
          ≈⟨ assoc ⟩
\end{code}
%</diagonal-in-u>

%<*diagonal-in-u1>
\begin{code}
            (f ∘ eval) ∘ (⟨ ϕ × id ⟩ ∘ ⟨ u , u ⟩)
\end{code}
%</diagonal-in-u1>

%<*diagonal-product-rearr>
\begin{code}
          ≈⟨ ∘-resp-r ⟨×⟩-∘-⟨,⟩ ⟩
            (f ∘ eval) ∘ ⟨ ϕ ∘ u , id ∘ u ⟩
          ≈⟨ ∘-resp-r (⟨,⟩-resp (≈.sym id-r) ≈.refl)  ⟩
            (f ∘ eval) ∘ ⟨ (ϕ ∘ u) ∘ id , id ∘ u ⟩
          ≈⟨ ∘-resp-r (≈.sym ⟨×⟩-∘-⟨,⟩)  ⟩
            (f ∘ eval) ∘ (⟨ (ϕ ∘ u) × id ⟩ ∘ ⟨ id , u ⟩)
          ≈⟨ unassoc ⟩
\end{code}
%</diagonal-product-rearr>

%<*diagonal-product-rearr1>
\begin{code}
            ((f ∘ eval) ∘ ⟨ (ϕ ∘ u) × id ⟩) ∘ ⟨ id , u ⟩
\end{code}
%</diagonal-product-rearr1>

%<*diagonal-curryuncurry>
\begin{code}
          ≈⟨ ∘-resp-l (∘-resp-r (⟨×⟩-resp (≈.sym curry∘uncurry) ≈.refl )) ⟩
\end{code}
%</diagonal-curryuncurry>

%<*diagonal-curryuncurry1>
\begin{code}
            ((f ∘ eval) ∘ ⟨ (curry (uncurry (ϕ ∘ u))) × id ⟩) ∘ ⟨ id , u ⟩
\end{code}
%</diagonal-curryuncurry1>

%<*diagonal-eval-curry>
\begin{code}
          ≈⟨ ∘-resp-l assoc ⟩
            (f ∘ (eval ∘ ⟨ (curry (uncurry (ϕ ∘ u))) × id ⟩)) ∘ ⟨ id , u ⟩
          ≈⟨ ∘-resp-l (∘-resp-r eval-curry) ⟩
\end{code}
%</diagonal-eval-curry>

%<*diagonal-eval-curry1>
\begin{code}
            (f ∘ (uncurry (ϕ ∘ u))) ∘ ⟨ id , u ⟩
\end{code}
%</diagonal-eval-curry1>

%<*diagonal-ax1-iso>
\begin{code}
           ≈⟨ assoc ⟩
             (f ∘ ((uncurry (ϕ ∘ u)) ∘ ⟨ id , u ⟩))
           ≈⟨ ∘-resp-r (∘-resp-l (≈.sym id-r)) ⟩
             (f ∘ (((uncurry (ϕ ∘ u)) ∘ id) ∘ ⟨ id , u ⟩))
           ≈⟨ ∘-resp-r (∘-resp-l (∘-resp-r (≈.sym One×A⇒A))) ⟩
\end{code}
%</diagonal-ax1-iso>

%<*diagonal-ax1-iso1>
\begin{code}
             (f ∘ (((uncurry (ϕ ∘ u)) ∘ oneIso ∘ otherIso) ∘ ⟨ id , u ⟩))
\end{code}
%</diagonal-ax1-iso1>

%<*diagonal-iso-app>
\begin{code}
           ≈⟨ ∘-resp-r (∘-resp-l unassoc) ⟩
             (f ∘ ((((uncurry (ϕ ∘ u)) ∘ oneIso) ∘ otherIso) ∘ ⟨ id , u ⟩))
           ≈⟨  ≈.refl ⟩
             (f ∘ (((collapseToOne (uncurry (ϕ ∘ u))) ∘ otherIso) ∘ ⟨ id , u ⟩))
           ≈⟨ ∘-resp-r assoc ⟩
             (f ∘ (((collapseToOne (uncurry (ϕ ∘ u)))) ∘ (otherIso ∘ ⟨ id , u ⟩)))
           ≈⟨ ≈.refl ⟩
\end{code}
%</diagonal-iso-app>

%<*diagonal-iso-app1>
\begin{code}
             (f ∘ (((collapseToOne (uncurry (ϕ ∘ u)))) ∘ (projr ∘ ⟨ id , u ⟩)))
\end{code}
%</diagonal-iso-app1>

%<*diagonal-proj-out>
\begin{code}
           ≈⟨ ∘-resp-r (∘-resp-r ⟨,⟩-projr) ⟩
             (f ∘ (((collapseToOne (uncurry (ϕ ∘ u)))) ∘ u ))
\end{code}
%</diagonal-proj-out>

%<*diagonal-end>
\begin{code}
           ≈⟨ ≈.refl ⟩
             f ∘ fixedPoint
           ∎
\end{code}
%</diagonal-end>

%<*diagonal-record>
\begin{code}
  in record { X = fixedPoint ; isFixedPoint = ≈.sym proof }
\end{code}
%</diagonal-record>
\end{AgdaAlign}

%<*diagonal-cantor>
\begin{code}
cantor : {A B : Obj} → ¬ FixedPointProperty B → ¬ PointSurjective A (A ↝ B)
cantor = contraposition lawvere
\end{code}
%</diagonal-cantor>

\end{document}
