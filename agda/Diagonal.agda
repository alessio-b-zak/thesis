open import Cats.Category.Constructions.CCC
open import Relation.Binary.PropositionalEquality 
open import Relation.Binary.PropositionalEquality.Core
open import Cats.Category.Base
open import Points
open import Cats.Category.Constructions.Product
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Exponential
open import Extension


module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC) 
  open HasBinaryProducts hasBinaryProducts
  open Points.Build C
  open Extension.Ext C {{hasBinaryProducts}} 

 
  module _ (A B : Obj) where

    diagonal : PointSurjective A (A ↝ B) → FixedPointProperty B
    diagonal record { arr = ϕ ; isPointSurjective = isPointSurjective } f =
      let
          h =  (curry (extendToOne (f ∘ eval ∘ ⟨ ϕ × id ⟩ ∘ δ )))
          ps = isPointSurjective h
          u = (HasSolution.X ps)
          t = HasSolution.isSolution ps
          -- t : ϕ ∘ u ≈ h
          ﹝ϕ∘u﹞ = ( collapseToOne (uncurry (ϕ ∘ u)))
          fixedPoint = ﹝ϕ∘u﹞ ∘ u
      in record { X = fixedPoint ; isFixedPoint = {!!} }










    -- f ∘ eval ∘ <ϕ idₐ> ∘ δ
    -- construct pullback of f to A then use ps property
    -- 

-- Open CCC, postulate - point surjective function
-- PS A Bᴬ → {x :  Endo B} → FixedPoint x
