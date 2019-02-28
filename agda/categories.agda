module categories where

open import Relation.Binary
open import Data.Bool
open import Data.Nat hiding (_⊔_)

open import Relation.Binary.PropositionalEquality
open import Level

record Category (a : Level) : Set (Level.suc (Level.suc a)) where
  field
    -- Levels are probably messed up
    Obj : Set (Level.suc a)
    _↣_ : Rel Obj a
--    _∘_  : {A B C : Obj} → (B ↣ C) → (A ↣ B) → (A ↣ C)
--    ι : {X : Obj} → (X ↣ X)
--
--  field
--    ∘-assoc : {A B C D : Obj}{f : A ↣ B}{g : B ↣ C}{h : C ↣ D}
--            → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
--    ι-left-neutral : {A B : Obj}{f : A ↣ B} → ι ∘ f ≡ f
--    ι-right-neutral : {A B : Obj}{f : A ↣ B} → f ∘ ι ≡ f


record Monoid (a : Level) : Set (Level.suc a) where
  field
    Underlying : Set a 
    _◓_ : Underlying → Underlying → Underlying
    𝑒 : Underlying
  field
    ◓-assoc : (a b c : Underlying) → ((a ◓ b) ◓ c) ≡ (a ◓ (b ◓ c))
    𝑒-left-neutral : {a : Underlying} → 𝑒 ◓ a ≡ a
    𝑒-right-neutral : {a : Underlying} → a ◓ 𝑒 ≡ a

record MonoidHomomorphism {L L'} (M : Monoid L) (M' : Monoid L') : Set ( L ⊔ L') where
  open Monoid M
  open Monoid M' renaming ( 𝑒 to 𝑒'; _◓_ to _◓'_ ; Underlying to Underlying')
  field
    f : Underlying → Underlying'
    𝑒-preserved : f 𝑒 ≡ 𝑒'
    ◓-preserved : {X Y : Underlying} → (f (X ◓ Y)) ≡ (f X ◓' f Y)


zero-left-neutral : {a : ℕ} → ℕ.zero + a ≡ a
zero-left-neutral = refl

zero-right-neutral : {a : ℕ} → a + ℕ.zero ≡ a
zero-right-neutral {ℕ.zero} = refl
zero-right-neutral {ℕ.suc a} = cong ℕ.suc (zero-right-neutral)

+-assoc : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
+-assoc ℕ.zero b c = refl
+-assoc (ℕ.suc a) b c = cong ℕ.suc (+-assoc a b c) 

nat-mon : Monoid Level.zero
nat-mon = record { Underlying = ℕ ;
                  _◓_ = _+_;
                  𝑒 = ℕ.zero;
                  𝑒-right-neutral = zero-right-neutral;
                  𝑒-left-neutral = zero-left-neutral;
                  ◓-assoc  = +-assoc}
                    

mon : {a : Level} → Category a 
mon {a} = record { Obj = Monoid a; _↣_ = MonoidHomomorphism}
