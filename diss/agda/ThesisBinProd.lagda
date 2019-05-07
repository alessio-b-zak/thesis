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
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)
open import Data.Bool using (Bool ; true ; false ; not; if_then_else_)
open import Relation.Binary.Core using (IsEquivalence)
open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Terminal as Terminal using (HasTerminal)
open import Cats.Functor using (Functor)
open import Cats.Util.Conv
open import Cats.Util.Logic.Constructive
open import Cats.Category.Constructions.Product hiding (HasBinaryProducts)

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Unique as Unique


\end{code}


%<*binprod-has-binary-products>
\begin{code}
record HasBinaryProducts {lo la l≈} (C : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
\end{code}
%</binprod-has-binary-products>

\begin{code}
  private open module Bld = Build C using (BinaryProduct ; Product)
  open Category C
  open ≈-Reasoning

  infixr 2 _×_ _×′_ ⟨_×_⟩ ⟨_,_⟩
\end{code}

%<*binprod-times>
\begin{code}
  field
    _×′_ : ∀ A B → BinaryProduct A B
\end{code}
%</binprod-times>

%<*binprod-obj>
\begin{code}
  _×_ : Obj → Obj → Obj
\end{code}
%</binprod-obj>

\begin{code}
  A × B = (A ×′ B) ᴼ
\end{code}


%<*binprod-projl>
\begin{code}
  projl : ∀ {A B} → A × B ⇒ A
\end{code}
%</binprod-projl>

\begin{code}
  projl {A} {B} = Product.proj (A ×′ B) true
\end{code}

%<*binprod-projr>
\begin{code}
  projr : ∀ {A B} → A × B ⇒ B
\end{code}
%</binprod-projr>

\begin{code}
  projr {A} {B} = Product.proj (A ×′ B) false
\end{code}


%<*binprod-unique-arr>
\begin{code}
  ⟨_,_⟩ : ∀ {A B Z} → Z ⇒ A → Z ⇒ B → Z ⇒ A × B
\end{code}
%</binprod-unique-arr>
\begin{code}
  ⟨_,_⟩ {A} {B} f g
    = Bld.factorizer (A ×′ B) (Bool-elim f g)
\end{code}


%<*binprod-unique-pair>
\begin{code}
  ⟨_×_⟩ : ∀ {A B A′ B′} → A ⇒ A′ → B ⇒ B′ → A × B ⇒ A′ × B′
\end{code}
%</binprod-unique-pair>


\begin{code}
  ⟨_×_⟩ {A} {B} {A′} {B′} f g
    = Bld.times (A ×′ B) (A′ ×′ B′) (Bool-elim f g)
\end{code}

\end{document}
