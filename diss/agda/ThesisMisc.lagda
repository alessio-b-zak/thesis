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
module ThesisMisc where
data A : Set where
  a : A

data B : Set where
 b : B 
\end{code}

\begin{code}
t = a
M = b
\end{code}

%<*misc-name>
\begin{code}
name : A
name = t
\end{code}
%</misc-name>

%<*misc-pi>
\begin{code}
foo : (x : A) → B
foo x = M
\end{code}
%</misc-pi>

%<*misc-pi'>
\begin{code}
foo' : (y : A) → B
foo' x = M
\end{code}
%</misc-pi'>

\begin{code}
open import Data.Nat hiding (_⊔_)
open import Level renaming (zero to lzero ; suc to lsuc)
infix 9 _≡_
\end{code}

%<*misc-inductive1>
\begin{code}
data InductiveType (Parameter : Set) : (Index : ℕ) → Set where
  Constructor1 : InductiveType Parameter 0
  Constructor2 : InductiveType Parameter 1
\end{code}
%</misc-inductive1>

%<*misc-inductive>
\begin{code}
data Vec {a : Level} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
\end{code}
%</misc-inductive>

%<*misc-sigma>
\begin{code}
data Σ {n m : Level} (A : Set n) (B : A → Set m) : Set (m ⊔ n) where
  _,_ : (a : A) → (B a) → Σ A B
\end{code}
%</misc-sigma>

%<*misc-product>
\begin{code}
data _×_ {m n : Level} (A : Set m) (B : Set n) : Set (m ⊔ n) where
  _,,_ : A → B → A × B
\end{code}
%</misc-product>

%<*misc-coproduct>
\begin{code}
data _⊎_ {m n} (A : Set m) (B : Set n) : Set (m ⊔ n) where
  inl : A  → A ⊎ B
  inr : B → A ⊎ B
\end{code}
%</misc-coproduct>

%<*misc-projl>
\begin{code}
projl : {m n : Level} → {A : Set m} → {B : Set n} → A × B → A
projl (x ,, x₁) = x
\end{code}
%</misc-projl>


%<*misc-equality>
\begin{code}
data _≡_ {m : Level} {A : Set m} (x : A) : A → Set m where
  refl : x ≡ x
\end{code}
%</misc-equality>


%<*misc-monoid>
\begin{code}
record Monoid (a : Level) : Set (lsuc a) where
  field
    S : Set a
    _∙_ : S → S → S
    e : S
  field
    ∙-assoc : (a b c : S) → ((a ∙ b) ∙ c) ≡ (a ∙ (b ∙ c))
    e-left-neutral : {a : S} → e ∙ a ≡ a
    e-right-neutral : {a : S} → a ∙ e ≡ a

\end{code}
%</misc-monoid>


%<*misc-monhom>
\begin{code}
record MonHom {L L'} (M : Monoid L) (M' : Monoid L') : Set ( L ⊔ L') where
\end{code}
%</misc-monhom>

\begin{code}
  open Monoid M
  open Monoid M' renaming ( e to e'; _∙_ to _∙'_ ; S to S')
\end{code}

%<*misc-monhom1>
\begin{code}
  field
    f : S → S'
    e-preserved : f e ≡ e'
    ∙-preserved : (X Y : S) → (f (X ∙ Y)) ≡ (f X ∙' f Y)
\end{code}
%</misc-monhom1>

\end{document}
