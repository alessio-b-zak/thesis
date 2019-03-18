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
                -- isos
                ≈⟨ ∘-resp-l collapse-unc-ps-proof ⟩ 
                  (collapseToOne (uncurry (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ ))))) ∘ u
                ≈⟨ ∘-resp-l (∘-resp-l uncurry∘curry) ⟩
                  (collapseToOne (extendToOne ( f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ))) ∘ u
                ≈⟨ ∘-resp-l (collapseExtendIso) ⟩
                  ( f ∘ (eval ∘ (⟨ ϕ × id ⟩ ∘ δ))) ∘ u
                -- reassos
                ≈⟨ ∘-resp-l unassoc ⟩
                  ( (f ∘ eval) ∘ ((⟨ ϕ × id ⟩) ∘ δ)) ∘ u
                ≈⟨ ∘-resp-l unassoc ⟩
                  ( ((f ∘ eval) ∘ (⟨ ϕ × id ⟩)) ∘ δ) ∘ u
                ≈⟨ ∘-resp-l (∘-resp-l assoc) ⟩
                  ( (f ∘ (eval ∘ ⟨ ϕ × id ⟩)) ∘ δ) ∘ u
                ≈⟨ assoc ⟩
                -- proof
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (δ ∘ u)
                ≈⟨ ≈.refl ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ ⟨ id , id ⟩ ∘ u
                ≈⟨ ∘-resp-r ⟨,⟩-∘ ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ (⟨ (id ∘ u) , (id ∘ u) ⟩)
                ≈⟨ ∘-resp-r (⟨,⟩-resp id-l id-l) ⟩
                  ( f ∘ eval ∘ ⟨ ϕ × id ⟩) ∘ ⟨ u , u ⟩
                -- reassoc
                ≈⟨ ∘-resp-l unassoc ⟩
                  ((f ∘ eval) ∘ ⟨ ϕ × id ⟩) ∘ ⟨ u , u ⟩
                ≈⟨ assoc ⟩
                --proof
                  (f ∘ eval) ∘ (⟨ ϕ × id ⟩ ∘ ⟨ u , u ⟩)
                ≈⟨ ∘-resp-r ⟨×⟩-∘-⟨,⟩ ⟩
                  (f ∘ eval) ∘ ⟨ ϕ ∘ u , id ∘ u ⟩
                ≈⟨ ∘-resp-r (⟨,⟩-resp (≈.sym id-r) ≈.refl)  ⟩
                  (f ∘ eval) ∘ ⟨ (ϕ ∘ u) ∘ id , id ∘ u ⟩
                ≈⟨ ∘-resp-r (≈.sym ⟨×⟩-∘-⟨,⟩)  ⟩
                  (f ∘ eval) ∘ (⟨ (ϕ ∘ u) × id ⟩ ∘ ⟨ id , u ⟩)
                ≈⟨ unassoc ⟩
                  ((f ∘ eval) ∘ ⟨ (ϕ ∘ u) × id ⟩) ∘ ⟨ id , u ⟩
                ≈⟨ ∘-resp-l (∘-resp-r (⟨×⟩-resp (≈.sym curry∘uncurry) ≈.refl )) ⟩
                  ((f ∘ eval) ∘ ⟨ (curry (uncurry (ϕ ∘ u))) × id ⟩) ∘ ⟨ id , u ⟩
                ≈⟨ ∘-resp-l assoc ⟩
                  (f ∘ (eval ∘ ⟨ (curry (uncurry (ϕ ∘ u))) × id ⟩)) ∘ ⟨ id , u ⟩
                ≈⟨ ∘-resp-l (∘-resp-r eval-curry) ⟩
                  (f ∘ (uncurry (ϕ ∘ u))) ∘ ⟨ id , u ⟩
                ≈⟨ assoc ⟩
                  (f ∘ ((uncurry (ϕ ∘ u)) ∘ ⟨ id , u ⟩))
                ≈⟨ ∘-resp-r (∘-resp-l (≈.sym id-r)) ⟩
                  (f ∘ (((uncurry (ϕ ∘ u)) ∘ id) ∘ ⟨ id , u ⟩))
                ≈⟨ ∘-resp-r (∘-resp-l (∘-resp-r (≈.sym One×A⇒A))) ⟩
                  (f ∘ (((uncurry (ϕ ∘ u)) ∘ oneIso ∘ otherIso) ∘ ⟨ id , u ⟩))
                ≈⟨ ∘-resp-r (∘-resp-l unassoc) ⟩
                  (f ∘ ((((uncurry (ϕ ∘ u)) ∘ oneIso) ∘ otherIso) ∘ ⟨ id , u ⟩))
                ≈⟨  ≈.refl ⟩
                  (f ∘ (((collapseToOne (uncurry (ϕ ∘ u))) ∘ otherIso) ∘ ⟨ id , u ⟩))
                ≈⟨ ∘-resp-r assoc ⟩
                  (f ∘ (((collapseToOne (uncurry (ϕ ∘ u)))) ∘ (otherIso ∘ ⟨ id , u ⟩)))
                ≈⟨ ≈.refl ⟩
                  (f ∘ (((collapseToOne (uncurry (ϕ ∘ u)))) ∘ (projr ∘ ⟨ id , u ⟩)))
                ≈⟨ ∘-resp-r (∘-resp-r ⟨,⟩-projr) ⟩
                  f ∘ fixedPoint
                ∎
          in record { X = fixedPoint ; isFixedPoint = ≈.sym proof }
    -- ~ ﹝h﹞ ∘ u
          -- ~ f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ ∘ u   
          -- ~ f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ ⟨ u × u ⟩
          -- ~ f ∘ eval ∘ ⟨ ϕ ∘ u × u ⟩
          -- ...
          -- ~ f ∘ ﹝ϕ∘u﹞ ∘ u 
