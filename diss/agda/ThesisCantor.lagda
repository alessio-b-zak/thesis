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
module ThesisCantor where

open import Cats.Category.Constructions.Terminal as Terminal
open import Cats.Category.Constructions.Product as Product
open import Cats.Category.Constructions.CCC as CCC
open import Data.Nat
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Cats.Category.Constructions.Exponential as Exponential
open import Cats.Category.Sets using (Sets)
open import Data.Bool using (true ; false; Bool)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Extension
open import Diagonal
import Points
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
import Cats.Category.Constructions.Unique as Unique
open import Cats.Category.Cat.Facts
open import Relation.Binary.PropositionalEquality

-- derivation of cantor's diagonal argument from lawvere's fixed pt thm
\end{code}


%<*cantor-univ>
\begin{code}
Sets1 = Sets lzero
\end{code}
%</cantor-univ>

\begin{code}
open Terminal.Build Sets1 hiding (terminal-unique)
open Unique.Build Sets1
open Points.Build Sets1
\end{code}

%<*cantor-pair>
\begin{code}
data Pair (A : Set) (B : Set) : Set where
  mkPair : A → B → Pair A B
\end{code}
%</cantor-pair>



%\begin{code}
%proj-uniqueness : ∀ {X} (A B : Set) (p : ∀ i → X → Bool-elim A B i) →
%                ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
%\end{code}

\begin{code}
proj-pair : ∀ {A B} i → Pair A B → Bool-elim A B i
proj-pair false (mkPair x x₁) = x₁
proj-pair true (mkPair x x₁) = x
\end{code}

%<*cantor-proj-sat>
\begin{code}
proj-sat-univ : {A B X : Set} → {x₁ : X}{i : Bool}
  → {x : (j : Bool) → X → Bool-elim A B j}
  → x i x₁ ≡ proj-pair {A} {B} i (mkPair (x true x₁) (x false x₁))
\end{code}
%</cantor-proj-sat>

\begin{code}
proj-sat-univ {A} {B} {X} {x₁} {false} {x} = refl
proj-sat-univ {A} {B} {X} {x₁} {true} {x} = refl

\end{code}

\begin{code}
pairPrf : {X A B : Set} → {g : X → Pair A B} → {y : X}
  → mkPair (proj-pair true (g y)) (proj-pair false (g y)) ≡ g y
pairPrf {X} {A} {B} {g₁} {y} with (g₁ y)
... | mkPair x x₁ = refl

\end{code}

%\begin{code}
%proj-uniqueness A B p =
%  let v = λ x → mkPair (p true x) (p false x)
%  in Unique.Build.∃!-intro v (λ i b → proj-pair-prf {A} {{!B!}} {_} {b} {{!!}} {{!!}} ) {!!}
%\end{code}

\begin{code}
mkPair-resp : {X Y : Set} → {x x₁ : X} → {y y₁ : Y}
  → (x ≡ x₁) → (y ≡ y₁) → mkPair x y ≡ mkPair x₁ y₁
mkPair-resp {X} {Y} {x} {.x} {y} {.y} refl refl = refl

\end{code}



%<*cantor-unique>
\begin{code}
proj-unique''' : {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
              {g : X → Pair A B} →
              (∀ i (x₁ : X) → x i x₁ ≡ proj-pair i (g x₁)) →
              (x₁ : X) →
              mkPair (x true x₁) (x false x₁) ≡ g x₁
\end{code}
%</cantor-unique>

\begin{code}
proj-unique : {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
               {g : X → Pair A B} →
               (h : ∀ i (x₁ : X) → x i x₁ ≡ proj-pair i (g x₁)) →
               (x₁ : X) → mkPair (x true x₁) (x false x₁) ≡ g x₁
proj-unique {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q = trans {!!} {!!}
\end{code}

\begin{code}
proj-unique''' {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q  = trans (mkPair-resp p q) (pairPrf {X} {A} {B} {g₁})
\end{code}

%<*cantor-unique-type>
\begin{code}
proj-uniqueness : ∀ {A B X} (p : ∀ i → X → Bool-elim A B i) →
  ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
\end{code}
%</cantor-unique-type>

%<*cantor-unique-def>
\begin{code}
proj-uniqueness {A} {B} = λ p →
  let u = (λ x → mkPair (p true x) (p false x))
  in Unique.Build.∃!-intro u
                           {!!}
                           {!!}
\end{code}
%</cantor-unique-def>

\begin{code}
proj-uniqueness' : ∀ {A B X} (p : ∀ i → X → Bool-elim A B i) →
  ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
proj-uniqueness' {A} {B} = λ p →
  let u = (λ x → mkPair (p true x) (p false x))
  in
\end{code}

%<*cantor-unique-def1>
\begin{code}
   Unique.Build.∃!-intro
    u
    (λ i b → proj-sat-univ {A} {B} {_} {b} {i} {p})
    {!!}
\end{code}
%</cantor-unique-def1>

\begin{code}
instance
  setsHasBinaryProducts : HasBinaryProducts (Sets1)
  setsHasBinaryProducts
    = record { _×′_ = λ A B →
             record { prod = Pair A B ;
                      proj = proj-pair ;
                      isProduct = proj-uniqueness }}
\end{code}

%= record { _×′_ = λ A B →
%record { prod = Pair A B ;
%proj = proj-pair ;
%isProduct = proj-uniqueness A B}
%}



%<*cantor-terminal-arrow>
\begin{code}
terminal-arrow : {X : Set} → X → ⊤
terminal-arrow x = ⊤.tt
\end{code}
%</cantor-terminal-arrow>

%<*cantor-terminal-unique>
\begin{code}
terminal-unique :  {X : Set} {g : X → ⊤} → ⊤ → (x : X) → ⊤.tt ≡ g x
terminal-unique x x₁ = refl
\end{code}
%</cantor-terminal-unique>

%<*cantor-terminal-prop1>
\begin{code}
terminal-property :  (X : Set) → ∃! X ⊤
terminal-property X =
  Unique.Build.∃!-intro {!!} _ {!!}
\end{code}
%</cantor-terminal-prop1>

\begin{code}
terminal-property' :  (X : Set) → ∃! X ⊤
terminal-property' X = Unique.Build.∃!-intro terminal-arrow _ {!!}
\end{code}

\begin{code}
terminal-property'' :  (X : Set) → ∃! X ⊤
terminal-property'' X =
\end{code}
%<*cantor-terminal-prop2>
\begin{code}
  Unique.Build.∃!-intro terminal-arrow _ terminal-unique
\end{code}
%</cantor-terminal-prop2>

%<*cantor-tisterminal>
\begin{code}
⊤-isTerminal : IsTerminal ⊤
⊤-isTerminal = terminal-property
\end{code}
%</cantor-tisterminal>


\begin{code}
instance
  setsHasTerminal : HasTerminal (Sets1)
  setsHasTerminal = record { One = ⊤ ; isTerminal = ⊤-isTerminal}
\end{code}

\end{document}
