module Extra where

open import Level
import Cats.Category.Constructions.Iso as Iso
open import Cats.Category.Base
open import Diagonal renaming (diagonal to lawvere)
open import Cats.Category.Constructions.CCC
open import Cats.Category.Constructions.Exponential
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Product
open import Data.Product hiding (uncurry ; curry)
open import Cats.Util.Conv
open import Extension
import Points
import Retract

import Relation.Binary.EqReasoning as EqReasoning

module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC)
  open HasTerminal (HasFiniteProducts.hasTerminal (IsCCC.hasFiniteProducts isCCC))
  open HasBinaryProducts (HasExponentials.hasBinaryProducts (IsCCC.hasExponentials isCCC))
  open Iso.Build C
  open ≈-Reasoning
  open Points.Build C
  open Extension.Build C

  module _ {X : Obj} {ps : PointSurjective X (X ↝ X)} where

    open module PS = PointSurjective ps
    _◎_ : (A : Point X) → (B : Point X) → (Point X)
    a ◎ b = eval ∘ ⟨ PS.arr × id ⟩ ∘ (⟨ a , b ⟩)

    fixedPointProperty : FixedPointProperty X
    fixedPointProperty = lawvere C ps

    Y-co : (f : Point X) → Σ (Point X) (λ x → f ◎ x ≈ x)
    Y-co f = let x = (PS.arr) ∘ f
                 y = uncurry x
                 z = collapseToOne y
                 q = fixedPointProperty z
                 h = HasFixedPoint.X q
                 foo = HasFixedPoint.isFixedPoint q
                 proof = begin
                           f ◎ h
                         ≈⟨ ≈.refl ⟩
                           eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ f , h ⟩
                         ≈⟨ ∘-resp-r ⟨×⟩-∘-⟨,⟩ ⟩
                           eval ∘ ⟨ (PS.arr ∘ f) , (id ∘ h) ⟩
                         ≈⟨ ∘-resp-r (⟨,⟩-resp (≈.sym id-r) ≈.refl)  ⟩
                           eval ∘ ⟨ (PS.arr ∘ f) ∘ id , id ∘ h ⟩
                         ≈⟨ ∘-resp-r (≈.sym ⟨×⟩-∘-⟨,⟩)  ⟩
                           eval ∘ ⟨ (PS.arr ∘ f) × id ⟩ ∘ ⟨ id , h ⟩
                         ≈⟨ unassoc ⟩
                           (eval ∘ ⟨ (PS.arr ∘ f) × id ⟩) ∘ ⟨ id , h ⟩
                         ≈⟨ ∘-resp-l (∘-resp-r (⟨×⟩-resp (≈.sym curry∘uncurry) ≈.refl )) ⟩
                           (eval ∘ ⟨ (curry (uncurry (PS.arr ∘ f))) × id ⟩) ∘ ⟨ id , h ⟩
                         ≈⟨ ∘-resp-l eval-curry ⟩
                            (uncurry (PS.arr ∘ f)) ∘ ⟨ id , h ⟩
                         ≈⟨ ∘-resp-l (≈.sym id-r) ⟩
                           (uncurry (PS.arr ∘ f) ∘ id) ∘ ⟨ id , h ⟩
                         ≈⟨ ∘-resp-l (∘-resp-r (≈.sym One×A⇒A)) ⟩
                           (uncurry (PS.arr ∘ f) ∘ oneIso ∘ otherIso) ∘ ⟨ id , h ⟩
                         ≈⟨ ∘-resp-l unassoc ⟩
                           ((uncurry (PS.arr ∘ f) ∘ oneIso) ∘ otherIso) ∘ ⟨ id , h ⟩
                         ≈⟨ assoc ⟩
                           (uncurry (PS.arr ∘ f) ∘ oneIso) ∘ (otherIso ∘ ⟨ id , h ⟩)
                         ≈⟨ ≈.refl ⟩
                           (collapseToOne (uncurry (PS.arr ∘ f))) ∘ (projr ∘ ⟨ id , h ⟩)
                         ≈⟨ ∘-resp-r ⟨,⟩-projr ⟩
                           (collapseToOne (uncurry (PS.arr ∘ f))) ∘ h
                         ≈⟨ foo ⟩
                          h
                         ∎
             in h , proof

