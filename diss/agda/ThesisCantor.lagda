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
open import Data.Unit.Base using (⊤)
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
open Terminal.Build Sets1
open Unique.Build Sets1
open Points.Build Sets1
\end{code}

%<*cantor-pair>
\begin{code}
data Pair (A : Set) (B : Set) : Set where
  mkPair : A → B → Pair A B
\end{code}
%</cantor-pair>

%<*cantor-proj>
\begin{code}
proj-pair : ∀ {A B} i → Pair A B → Bool-elim A B i
proj-pair false (mkPair x y) = y
proj-pair true (mkPair x y) = x
\end{code}
%</cantor-proj>


%<*cantor-unique-type>
\begin{code}
proj-uniqueness : ∀ {A B X} (p : ∀ i → X → Bool-elim A B i) →
                ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
\end{code}
%</cantor-unique-type>

%<*cantor-unique-def>
\begin{code}
proj-uniqueness p
  = Unique.Build.∃!-intro (λ x → mkPair (p true x) (p false x)) {!!} {!!}
\end{code}
%</cantor-unique-def>

\begin{code}
instance
  setsHasBinaryProducts : HasBinaryProducts (Sets1)
  setsHasBinaryProducts
    = record { _×′_ = λ A B →
                    record { prod = Pair A B ;
                             proj = proj-pair ;
                             isProduct = proj-uniqueness }
             }
--    = record { _×′_ = λ A B →
--                      record { prod = Pair A B ;
--                        proj = proj-Sets1 ;
--                        isProduct = ?
--    }
--  }

\end{code}

\end{document}
