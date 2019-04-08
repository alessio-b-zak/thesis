module Extension where

open import Cats.Category.Base
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Product as Produdct using (HasBinaryProducts)
open import Cats.Category.Constructions.Terminal as Terminal using (HasTerminal)
import Cats.Category.Constructions.Exponential
import Cats.Category.Constructions.Unique as Unique
import Cats.Category.Constructions.Iso as Iso
open import Cats.Util.Conv

module Build {lo la l=} (C : Category lo la l=)
                      {{hasBinaryProducts : HasBinaryProducts C}}
                      {{hasTerminal : HasTerminal C}} where

  open Category C
  open HasBinaryProducts hasBinaryProducts
  open Iso.Build C
  open HasTerminal hasTerminal
  open Terminal.Build C
  open Unique.Build C
  open ≈-Reasoning


  δ : {A : Obj} → A ⇒ A × A
  δ = ⟨ id , id ⟩

  oneIso : {A : Obj} → A ⇒ (One × A)
  oneIso {A} = ⟨  isTerminal A ⃗ , id ⟩
 
  otherIso : {A : Obj} → (One × A ⇒ A)
  otherIso {A} = projr {One} {A}

  isoIso : {A : Obj} → otherIso ∘ oneIso ≈ id {A}
  isoIso {A} = begin
                 otherIso ∘ oneIso
               ≈⟨ ≈.refl ⟩
                 projr ∘ ⟨ isTerminal A ⃗ , id ⟩
               ≈⟨ ⟨,⟩-projr ⟩
                 id
               ∎

  One×A⇒A : {A : Obj} → (oneIso ∘ otherIso {A}) ≈ id {(One × A)}
  One×A⇒A {A} = begin
                   oneIso ∘ otherIso
                 ≈⟨ ≈.refl ⟩
                    ⟨ isTerminal A ⃗ , id ⟩  ∘ projr 
                 ≈⟨ ⟨,⟩-∘ ⟩
                    ⟨ ((isTerminal A ⃗) ∘ projr) , (id ∘ projr) ⟩
                 ≈⟨ ⟨,⟩-resp ≈.refl id-l ⟩
                    ⟨ ((isTerminal A ⃗) ∘ projr) , projr ⟩
                 ≈⟨ ⟨,⟩-resp (X⇒Terminal-unique isTerminal ) ≈.refl ⟩
                    ⟨ ((isTerminal (One × A) ⃗)) , projr ⟩
                ≈⟨ ⟨,⟩-resp (X⇒Terminal-unique isTerminal) ≈.refl ⟩
                    ⟨ projl , projr ⟩
                 ≈⟨ ⟨projr,projl⟩-id ⟩
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

  oneIsoA : ∀{A} →  (One × A) ≅ A
  oneIsoA = record { forth = otherIso ;
                     back = oneIso ;
                     back-forth = One×A⇒A ;
                     forth-back = isoIso }
