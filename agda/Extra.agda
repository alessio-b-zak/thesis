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
open import Cats.Category.Constructions.Unique as Unique
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
  open Unique.Build C
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



    util : (f : X ⇒ X) → Σ (Point X) (λ u → ∀ {b} → u ◎ b ≈ f ∘ b )
    util f = let f' = curry ( extendToOne(f))
                 sol = PS.isPointSurjective f'
                 open HasSolution sol renaming (X to q ; isSolution to q-prf)
              in q , λ {b} → begin
                               q ◎ b
                             ≈⟨ ≈.refl ⟩
                               eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ q , b ⟩
                             ≈⟨ ∘-resp-r ⟨×⟩-∘-⟨,⟩ ⟩
                               eval ∘ ⟨ PS.arr ∘ q , id ∘ b ⟩
                             ≈⟨ ∘-resp-r (⟨,⟩-resp (≈.sym id-r) ≈.refl)  ⟩
                               eval ∘ ⟨ (PS.arr ∘ q) ∘ id , id ∘ b ⟩
                             ≈⟨ ∘-resp-r (≈.sym ⟨×⟩-∘-⟨,⟩)  ⟩
                               eval ∘ ⟨ PS.arr ∘ q × id ⟩ ∘ ⟨ id , b ⟩
                             ≈⟨ unassoc ⟩
                               (eval ∘ ⟨ PS.arr ∘ q × id ⟩) ∘ ⟨ id , b ⟩
                             ≈⟨ ∘-resp-l (∘-resp-r (⟨×⟩-resp (≈.sym curry∘uncurry) ≈.refl )) ⟩
                               (eval ∘ ⟨ curry(uncurry(PS.arr ∘ q)) × id ⟩) ∘ ⟨ id , b ⟩
                             ≈⟨ ∘-resp-l eval-curry ⟩
                               uncurry (PS.arr ∘ q) ∘ ⟨ id , b ⟩
                             ≈⟨ ∘-resp-l (≈.sym id-r) ⟩
                               (uncurry (PS.arr ∘ q) ∘ id) ∘ ⟨ id , b ⟩
                             ≈⟨ ∘-resp-l (∘-resp-r (≈.sym One×A⇒A)) ⟩
                               (uncurry (PS.arr ∘ q) ∘ oneIso ∘ otherIso) ∘ ⟨ id , b ⟩
                             ≈⟨ ∘-resp-l unassoc ⟩
                               ((uncurry (PS.arr ∘ q) ∘ oneIso) ∘ otherIso) ∘ ⟨ id , b ⟩
                             ≈⟨ assoc ⟩
                               (uncurry (PS.arr ∘ q) ∘ oneIso) ∘ (otherIso ∘ ⟨ id , b ⟩)
                             ≈⟨ ∘-resp-r ⟨,⟩-projr ⟩
                               (collapseToOne (uncurry (PS.arr ∘ q))) ∘ b
                             ≈⟨ ∘-resp-l (collapseToOne-resp (uncurry-resp C {X} {X} q-prf)) ⟩
                               (collapseToOne (uncurry (curry( extendToOne( f))))) ∘ b
                             ≈⟨ ∘-resp-l (collapseToOne-resp uncurry∘curry) ⟩
                               (collapseToOne (extendToOne( f))) ∘ b
                             ≈⟨ ∘-resp-l collapseExtendIso ⟩
                               f ∘ b
                             ∎

    I-combin-exist : Σ (Point X) (λ i → ∀ {x} → i ◎ x ≈ x)
    I-combin-exist = let i = util id in proj₁ i , λ {x} → begin
                                                            (proj₁ i) ◎ x
                                                          ≈⟨ proj₂ i  ⟩
                                                            id ∘ x
                                                          ≈⟨ id-l ⟩
                                                            x
                                                          ∎


    M-combin-exist : Σ (Point X) (λ m → ∀ {x} → m ◎ x ≈ x ◎ x)
    M-combin-exist = let m = util (eval ∘ ⟨ PS.arr × id ⟩ ∘ δ)
                      in proj₁ m , λ {x} → begin
                                             (proj₁ m) ◎ x
                                           ≈⟨ proj₂ m ⟩
                                             (eval ∘ ⟨ PS.arr × id ⟩ ∘ δ) ∘ x
                                           ≈⟨ ∘-resp-l unassoc ⟩
                                             ((eval ∘ ⟨ PS.arr × id ⟩) ∘ δ) ∘ x
                                           ≈⟨ assoc ⟩
                                             (eval ∘ ⟨ PS.arr × id ⟩) ∘ (δ ∘ x)
                                           ≈⟨ ≈.refl ⟩
                                             (eval ∘ ⟨ PS.arr × id ⟩) ∘ (⟨ id , id ⟩ ∘ x)
                                           ≈⟨ ∘-resp-r ⟨,⟩-∘ ⟩
                                             (eval ∘ ⟨ PS.arr × id ⟩) ∘ (⟨ (id ∘ x) , (id ∘ x) ⟩)
                                           ≈⟨ ∘-resp-r (⟨,⟩-resp id-l id-l) ⟩
                                             (eval ∘ ⟨ PS.arr × id ⟩) ∘ (⟨ x , x ⟩)
                                           ≈⟨ assoc ⟩
                                             eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ x , x ⟩
                                           ≈⟨ ≈.refl ⟩
                                             x ◎ x
                                           ∎


    ◎-pres : ∀ {x y z} → x ≈ z → x ◎ y ≈ z ◎ y
    ◎-pres {x} {y} {z} prf = begin
                               x ◎ y
                             ≈⟨ ≈.refl ⟩
                               eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ x , y ⟩
                             ≈⟨ ∘-resp-r (∘-resp-r (⟨,⟩-resp prf ≈.refl)) ⟩
                               eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ z , y ⟩
                             ≈⟨ ≈.refl ⟩
                               z ◎ y
                             ∎

    F-combin-exist : Σ (Point X) (λ f → ∀ {x y} → (f ◎ x) ◎ y ≈ y)
    F-combin-exist = let y = curry {One} {X} (extendToOne(id))
                         sol = PS.isPointSurjective y
                         open HasSolution sol renaming (X to z ; isSolution to z-prf)
                         !D = isTerminal X
                         q = z ∘ (∃!′.arr !D)
                         snd = util q
                         in proj₁ snd , λ {x} {y} → begin
                                                      (proj₁ snd ◎ x) ◎ y
                                                    ≈⟨ ◎-pres (proj₂ snd) ⟩
                                                      (q ∘ x) ◎ y
                                                    ≈⟨  ≈.refl ⟩
                                                      eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ (q ∘ x) , y ⟩
                                                    ≈⟨  ≈.refl ⟩
                                                      eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ (z ∘ (∃!′.arr !D)) ∘ x , y ⟩
                                                    ≈⟨  ∘-resp-r (∘-resp-r (⟨,⟩-resp assoc ≈.refl)) ⟩
                                                      eval ∘ ⟨ PS.arr × id ⟩ ∘ ⟨ z ∘ (∃!′.arr !D) ∘ x , y ⟩
                                                    ≈⟨ {! ?!} ⟩
                                                      {!!}
                                                    ≈⟨ {! ?!} ⟩
                                                      y
                                                    ∎
