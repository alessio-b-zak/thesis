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
import Cats.Category.Constructions.Terminal as Terminal
open import Level
open import Cats.Category.Base
\end{code}
%<*terminal-def-has>
\begin{AgdaMultiCode}
\begin{code}
record HasTerminal {lo la l≈} (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈) where
\end{code}
\begin{code}[hide]
  open Category Cat
  open Terminal.Build Cat
\end{code}
\begin{code}
  field
    One : Obj
    isTerminal : IsTerminal One
\end{code}
\end{AgdaMultiCode}
%</terminal-def-has>
\end{document}
