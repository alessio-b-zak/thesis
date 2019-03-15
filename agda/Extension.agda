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
  open ≈-Reasoning

  open Cats.Category.Constructions.Product.Build

  δ : {A : Obj} → A ⇒ A × A
  δ = ⟨ id , id ⟩

  oneIso : {A : Obj} → A ⇒ (One × A)
  oneIso {A} = ⟨  isTerminal A ⃗ , id ⟩
 
  otherIso : {A : Obj} → (One × A ⇒ A)
  otherIso {A} = projr {One} {A}

  -- Use uniqueness proof of rhs 
  -- use proof of factorizer and time
  -- ∃′→≈ potensh
  ⟨×⟩-⟨,⟩-comp : {A B C D F : Obj} → {f : A ⇒ B} → {g : A ⇒ C} 
              → {h : B ⇒ D} → {i : C ⇒ F}
              → ⟨ h ∘ f , i ∘ g ⟩ ≈ ⟨ h × i ⟩ ∘ ⟨ f , g ⟩
  ⟨×⟩-⟨,⟩-comp {A} {B} {C₁} {D} {F} {f} {g} {h} {i} with (⟨ h ∘ f , i ∘ g ⟩)
  ... | p = let x = Unique.Build.∃!′.unique p in ?
--    let x = begin
--              ⟨ h × i ⟩ ∘ ⟨ f , g ⟩
--            ≈⟨ {!!} ⟩
--              ⟨ h ∘ f , i ∘ g ⟩
--            ∎ 
--
--    in ≈.sym x 
     
  isoIso : {A : Obj} → otherIso ∘ oneIso ≈ id {A}
  isoIso {A} = begin
                 otherIso ∘ oneIso
               ≈⟨ ≈.refl ⟩
                 projr ∘ ⟨ isTerminal A ⃗ , id ⟩
               ≈⟨ ⟨,⟩-projr ⟩
                 id
               ∎
                

  extendToOne  : ∀ {A B} → (A ⇒ B) → (One × A ⇒ B)
  extendToOne x = x ∘ otherIso

  collapseToOne : ∀ {A B} → (One × A ⇒ B) → (A ⇒ B)
  collapseToOne x = x ∘ oneIso

  collapseExtendIso :  {A B : Obj} {f : A ⇒ B} → collapseToOne (extendToOne f) ≈ f 
  collapseExtendIso {A} {B} {f} = begin
                                       (collapseToOne (extendToOne f))
                                  ≈⟨ ≈.refl ⟩
                                       (f ∘ otherIso) ∘ oneIso
                                  ≈⟨ assoc ⟩
                                       f ∘ (otherIso ∘ oneIso)
                                  ≈⟨ ∘-resp-r (isoIso) ⟩
                                       f ∘ id
                                  ≈⟨ id-r ⟩
                                       f
                                   ∎

  collapseToOne-resp : ∀ {A B} {u v : One × A ⇒ B}  → (u ≈ v) → (collapseToOne u) ≈ (collapseToOne v)
  collapseToOne-resp x = ∘-resp-l x
