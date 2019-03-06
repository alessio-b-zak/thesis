

open import Relation.Binary 
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Function hiding (id; _∘_)

open import Relation.Binary.PropositionalEquality
open import Level

record Category (a : Level) : Set (Level.suc (Level.suc a)) where
  field
    -- Levels are probably messed up
    Obj : Set (Level.suc a)
    _↣_ : Rel Obj a
    _∘_  : {A B C : Obj} → (B ↣ C) → (A ↣ B) → (A ↣ C)
    ι : {X : Obj} → (X ↣ X)
--
  field
    ∘-assoc : {A B C D : Obj}{f : A ↣ B}{g : B ↣ C}{h : C ↣ D}
            → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
    ι-left-neutral : {A B : Obj}{f : A ↣ B} → ι ∘ f ≡ f
    ι-right-neutral : {A B : Obj}{f : A ↣ B} → f ∘ ι ≡ f

open Category

record Monic {a : Level}{c : Category a}{B C : Obj c}(f : B ↣ C) : Set a where
  field
    proof : {A : Obj c} → (g h : A ↣ B) → (f ∘ g) ≡ (f ∘ h) → g ≡ h 

--moncat : {a : Level} → Category a
--moncat {a} = record { Obj = Monoid a; _↣_ = MonHom; ι = id-homo; _∘_  = MonoidComp; ι-left-neutral = {!!} }
