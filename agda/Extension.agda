module Extension where

open import Cats.Category.Base
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Product
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Exponential
import Cats.Category.Constructions.Unique as Unique

open import Cats.Util.Conv

module Ext {lo la l=} (C : Category lo la l=)
                      (hasFiniteProducts : HasFiniteProducts C) where

  open Category C


  open HasFiniteProducts hasFiniteProducts
  open Unique.Build C

  δ : {A : Obj} → A ⇒ A × A
  δ = ⟨ id , id ⟩

  oneIso : {A : Obj} → A ⇒ (One × A)
  oneIso {A} = ⟨  isTerminal A ⃗ , id ⟩
 
  otherIso : {A : Obj} → (One × A ⇒ A)
  otherIso {A} = projr {One} {A}

  bar  : ∀ {A B} → (A ⇒ B) → (One × A ⇒ B)
  bar x = x ∘ otherIso


 
