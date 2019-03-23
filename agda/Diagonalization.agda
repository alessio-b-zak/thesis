module Diagonalization where


import Points
open import Diagonal
open import Cats.Category.Base
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Exponential
import Cats.Category.Constructions.Iso as Iso


module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC)
  open Iso.Build C
  open Points.Build C
  open ≈-Reasoning


  funspaceRetract→PS : {B : Obj} → B ≅ (B ↝ B) → PointSurjective B (B ↝ B)
  funspaceRetract→PS record { forth = forth ; back = back ; back-forth = back-forth ; forth-back = forth-back }
    = record { arr = forth ;
               isPointSurjective = λ b
                 → record { X = back ∘ b ;
                            isSolution = begin
                                           forth ∘ back ∘ b
                                         ≈⟨ unassoc ⟩
                                           (forth ∘ back) ∘ b
                                         ≈⟨ ∘-resp-l forth-back ⟩
                                           id ∘ b
                                         ≈⟨ id-l ⟩
                                           b
                                         ∎ } }

  funspaceRetract→Fix : {B : Obj} → B ≅ (B ↝ B) → FixedPointProperty B
  funspaceRetract→Fix {B} x f = diagonal C ((funspaceRetract→PS {B} x)) f
