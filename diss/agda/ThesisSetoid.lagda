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
open import Relation.Binary.Core hiding (IsEquivalence )
infix 4 _≈_
\end{code}

%<*setoid-isequiv>
\begin{code}
record IsEquivalence {a l} {A : Set a}
  (_≈_ : Rel A l) : Set (a ⊔ l) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_
\end{code}
%</setoid-isequiv>

%<*setoid-setoid>
\begin{code}
record Setoid c l : Set (suc (c ⊔ l)) where
  field
    Carrier       : Set c
    _≈_           : Rel Carrier l
    isEquivalence : IsEquivalence _≈_
\end{code}
%</setoid-setoid>

\end{document}
