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

module ThesisSets where

open import Data.Product using (Σ ; _×_ ; proj₁ ; proj₂)
open import Level
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category.Base
open import Cats.Util.Function
open import Cats.Util.Logic.Constructive
\end{code}

\begin{code}
module _ {l} {A B : Set l} where
\end{code}

\begin{code}

  infixr 4 _≈_
\end{code}

%<*sets-equality>
\begin{code}
  _≈_ : (f g : A → B) → Set l
  f ≈ g = ∀ x → f x ≡ g x
\end{code}
%</sets-equality>

\begin{code}
  equiv : IsEquivalence _≈_
  equiv = record
    { refl = λ x → ≡.refl
    ; sym = λ eq x → ≡.sym (eq x)
    ; trans = λ eq₁ eq₂ x → ≡.trans (eq₁ x) (eq₂ x)
    }
\end{code}

\begin{code}
\end{code}


%<*sets-instance>
\begin{code}
instance Sets : ∀ l → Category (suc l) l l
Sets l = record
  { Obj = Set l ;
   _⇒_ = λ A B → A → B ;
\end{code}
%</sets-instance>

%<*sets-instance1>
\begin{code}
    _≈_ = _≈_ ;
    id = id ;
    _∘_ = _∘_ ;
\end{code}
%</sets-instance1>

\begin{code}
   equiv = equiv ;
   ∘-resp = λ {_} {_} {_} {f} eq₁ eq₂ x
             → ≡.trans (≡.cong f (eq₂ _)) (eq₁ _)
  ; id-r = λ _ → ≡.refl
  ; id-l = λ _ → ≡.refl
  ; assoc = λ _ → ≡.refl
  }
\end{code}

\end{document}
