module Extension where

open import Cats.Category.Base
open import Cats.Category.Constructions.Product

module Ext {lo la l=} (C : Category lo la l=) (hasBinaryProducts : HasBinaryProducts C) where

  open Category C
  open HasBinaryProducts hasBinaryProducts
  
  δ : {A : Obj} → A ⇒ A × A
  δ = ⟨ id , id ⟩


  -- create adjunction stuff
