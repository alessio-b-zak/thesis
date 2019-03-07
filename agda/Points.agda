module Points where

open import Cats.Category.Base
open import Level
open import Cats.Category.Constructions.Terminal as Terminal using (HasTerminal)


module Build {lo la l=} (C : Category lo la l=) {{hasTerminal : HasTerminal C}} where

  open Category C
  open HasTerminal hasTerminal 

  Point : Obj → Set la
  Point X = One ⇒ X

  IsFixedPoint : {B : Obj} → (f : B ⇒ B) → (s : Point B) → Set l=
  IsFixedPoint f s = f ∘ s ≈ s

  record HasFixedPoint {B : Obj} (f : B ⇒ B) : Set (lo ⊔ la ⊔ l=) where
    field
      X : Point B 
      isFixedPoint : IsFixedPoint f X 


  IsSolution : {A B : Obj} → (f : A ⇒ B) → (a : Point A) → (b : Point B) → Set l=
  IsSolution f a b = f ∘ a ≈ b
  

  record HasSolution {A B : Obj} (f : A ⇒ B) (b : Point B) : Set (lo ⊔ la ⊔ l=) where
    field
      X : Point A
      isSolution : IsSolution f X b 

  FixedPointProperty : Obj → Set (lo ⊔ la ⊔ l=)
  FixedPointProperty B = ∀ f → HasFixedPoint {B} f

  -- point surjective f : A ⇒ B if  ∀ (Point B) 
  IsPointSurjective : {A B : Obj} → (f : A ⇒ B) → Set (lo ⊔ la ⊔ l=)
  IsPointSurjective f = ∀ b → HasSolution f b

  record PointSurjective (A : Obj) (B : Obj) : Set (lo ⊔ la ⊔ l=) where

    field
      arr : (A ⇒ B)
      isPointSurjective : IsPointSurjective arr
   
