module Retract where

open import Level
import Cats.Category.Constructions.Iso as Iso
open import Cats.Category.Base

open import Cats.Util.Conv

import Relation.Binary.EqReasoning as EqReasoning



module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning


  record Retract (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      forth : A ⇒ B
      back : B ⇒ A
      forth-back : forth ∘ back ≈ id


open Build public
