open import Cats.Category.Constructions.CCC
open import Cats.Category.Base
open import Points
open import Cats.Category.Constructions.Product
open import Cats.Category.Constructions.Terminal
open import Cats.Category.Constructions.Exponential
open import Extension


module _ {lo la l=} (C : Category lo la l=) {{isCCC : IsCCC C}} where

  open Category C
  open HasExponentials (IsCCC.hasExponentials isCCC) 
  open HasFiniteProducts (IsCCC.hasFiniteProducts isCCC)
  open Points.Build C

  module _ (A B : Obj) where

    diagonal : PointSurjective A (A ↝ B) → FixedPointProperty B
    diagonal record { arr = ϕ ; isPointSurjective = isPointSurjective } f =
      let
          h = eval ∘ ⟨ ϕ × id ⟩ 
      in {!!}

    -- f ∘ eval ∘ <ϕ idₐ> ∘ δ
    -- construct pullback of f to A then use ps property
    -- 

-- Open CCC, postulate - point surjective function
-- PS A Bᴬ → {x :  Endo B} → FixedPoint x
