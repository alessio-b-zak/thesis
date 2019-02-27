module categories where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

record Category (a : Level) (Obj : Set a) : Set (suc a) where
  field
    -- Levels are probably messed up
    _↣_ : Rel Obj a
    _∘_  : {A B C : Obj} → (B ↣ C) → (A ↣ B) → (A ↣ C)
    ι : {X : Obj} → (X ↣ X)

  field
    ∘-assoc : {A B C D : Obj}{f : A ↣ B}{g : B ↣ C}{h : C ↣ D}
            → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
    ι-left-neutral : {A B : Obj}{f : A ↣ B} → ι ∘ f ≡ f
    ι-right-neutral : {A B : Obj}{f : A ↣ B} → f ∘ ι ≡ f

record Monoid (A : Set) : Set where
  field
    _◓_ : A → A → A
    𝑒 : A
  field
    ◓-assoc : {a b c : A} → ((a ◓ b) ◓ c) ≡ (a ◓ (b ◓ c))
    𝑒-left-neutral : {a : A} → 𝑒 ◓ a ≡ a
    𝑒-right-neutral : {a : A} → a ◓ 𝑒 ≡ a


