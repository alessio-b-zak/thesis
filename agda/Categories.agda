module Categories where

open import Relation.Binary 
open import Monoids
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Function hiding (id)

open import Relation.Binary.PropositionalEquality
open import Level

record Category (a : Level) : Set (Level.suc (Level.suc a)) where
  field
    -- Levels are probably messed up
    Obj : Set (Level.suc a)
    _↣_ : Rel Obj a
--    _∘_  : {A B C : Obj} → (B ↣ C) → (A ↣ B) → (A ↣ C)
    ι : {X : Obj} → (X ↣ X)
--
--  field
--    ∘-assoc : {A B C D : Obj}{f : A ↣ B}{g : B ↣ C}{h : C ↣ D}
--            → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
--    ι-left-neutral : {A B : Obj}{f : A ↣ B} → ι ∘ f ≡ f
--    ι-right-neutral : {A B : Obj}{f : A ↣ B} → f ∘ ι ≡ f
