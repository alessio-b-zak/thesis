module Extension where

open import Cats.Category.Base
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Product
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Exponential
import Cats.Category.Constructions.Unique as Unique

open import Cats.Util.Conv

module Ext {lo la l=} (C : Category lo la l=)
                      {{hasBinaryProducts : HasBinaryProducts C}}
                      {{hasTerminal : HasTerminal C}} where

  open Category C
  open HasBinaryProducts hasBinaryProducts
  open HasTerminal hasTerminal
  open Unique.Build C

  δ : {A : Obj} → A ⇒ A × A
  δ = ⟨ id , id ⟩

  oneIso : {A : Obj} → A ⇒ (One × A)
  oneIso {A} = ⟨  isTerminal A ⃗ , id ⟩
 
  otherIso : {A : Obj} → (One × A ⇒ A)
  otherIso {A} = projr {One} {A}

  extendToOne  : ∀ {A B} → (A ⇒ B) → (One × A ⇒ B)
  extendToOne x = x ∘ otherIso

  collapseToOne : ∀ {A B} → (One × A ⇒ B) → (A ⇒ B)
  collapseToOne x = x ∘ oneIso
   
