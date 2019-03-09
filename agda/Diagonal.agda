open import Cats.Category.Constructions.CCC
open import Cats.Category.Base
open import Points
open import Data.Bool
open import Cats.Category.Constructions.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Exponential
open import Extension


module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open ≈-Reasoning
  open HasExponentials (IsCCC.hasExponentials isCCC) 
  open HasBinaryProducts hasBinaryProducts
  open Points.Build C
  open Extension.Ext C {{hasBinaryProducts}} 

 
  module _ (A B : Obj) where


    ⟨×⟩-resp-f : ∀ {A B D} {f g : A ⇒ B ↝ D} → f ≈ g → ⟨ f × id {B} ⟩ ≈ ⟨ g × id {B} ⟩
    ⟨×⟩-resp-f x = ⟨×⟩-resp x ≈.refl

    uncurry-resp : ∀ {A B D} {f g : A ⇒ B ↝ D} → f ≈ g → uncurry f ≈ uncurry g 
    uncurry-resp {A} {B} {D} {f} {g} x = ∘-resp-r (⟨×⟩-resp-f {A} {B} {D} {f} {g} x)
    
    diagonal : PointSurjective A (A ↝ B) → FixedPointProperty B
    diagonal record { arr = ϕ ; isPointSurjective = isPointSurjective } f =
      let
          h =  (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )))
          ps = isPointSurjective h
          u = (HasSolution.X ps)
          ps-proof = HasSolution.isSolution ps
          unc-ps-proof = uncurry-resp ps-proof
          collapse-unc-ps-proof = collapseToOne-resp unc-ps-proof
          ﹝ϕ∘u﹞ = ( collapseToOne (uncurry (ϕ ∘ u)))
          fixedPoint = ﹝ϕ∘u﹞ ∘ u
          proof = begin fixedPoint
                ≈⟨ ∘-resp-l collapse-unc-ps-proof ⟩ 
                  (collapseToOne (uncurry (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ ))))) ∘ u
                ≈⟨ ∘-resp-l (∘-resp-l uncurry∘curry)⟩
                  (collapseToOne (extendToOne ( f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ))) ∘ u
                ≈⟨ ∘-resp-l (collapseExtendIso)  ⟩
                  ( f ∘ (eval ∘ (⟨ ϕ × id ⟩ ∘ δ))) ∘ u
                ≈⟨ ∘-resp-l unassoc  ⟩
                  ( (f ∘ eval) ∘ (⟨ ϕ × id ⟩ ∘ δ)) ∘ u
                ≈⟨ ∘-resp-l {!!} ⟩
                  ( (f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ δ) ∘ u
                ≈⟨ assoc  ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (δ ∘ u)
                ≈⟨ ≈.refl  ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (⟨ id , id ⟩ ∘ u)
                ≈⟨ {!!}  ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (⟨ (id ∘ u) , (id ∘ u) ⟩)
                ≈⟨ {!!} ⟩
                  f ∘ fixedPoint
                ∎
          in record { X = fixedPoint ; isFixedPoint = ≈.sym proof }
    -- ~ ﹝h﹞ ∘ u
          -- ~ f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ ∘ u   
          -- ~ f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ ⟨ u × u ⟩
          -- ~ f ∘ eval ∘ ⟨ ϕ ∘ u × u ⟩
          -- ...
          -- ~ f ∘ ﹝ϕ∘u﹞ ∘ u 
