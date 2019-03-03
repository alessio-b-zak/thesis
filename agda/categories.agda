module categories where

open import Relation.Binary 
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


record Monoid (a : Level) : Set (Level.suc a) where
  field
    Underlying : Set a 
    _◓_ : Underlying → Underlying → Underlying
    𝑒 : Underlying
  field
    ◓-assoc : (a b c : Underlying) → ((a ◓ b) ◓ c) ≡ (a ◓ (b ◓ c))
    𝑒-left-neutral : {a : Underlying} → 𝑒 ◓ a ≡ a
    𝑒-right-neutral : {a : Underlying} → a ◓ 𝑒 ≡ a


id : ∀ {a} {A : Set a} → A → A
id x = x

id-preserve : ∀ {a}(A : Set a) → (x : A) → (id x) ≡ x
id-preserve A x = refl

id-preserves-op : ∀ {a}{G : Set a} (_∘_ : G → G → G)(A B : G)  → id (A ∘ B) ≡ (id A) ∘ (id B)
id-preserves-op {a} {G} _∘_ A B  = refl


record MonHom {L L'} (M : Monoid L) (M' : Monoid L') : Set ( L ⊔ L') where
  open Monoid M
  open Monoid M' renaming ( 𝑒 to 𝑒'; _◓_ to _◓'_ ; Underlying to Underlying')
  field
    f : Underlying → Underlying'
    𝑒-preserved : f 𝑒 ≡ 𝑒'
    ◓-preserved : (X Y : Underlying) → (f (X ◓ Y)) ≡ (f X ◓' f Y)

id-pres-id : ∀ {a b c} → (M : Monoid a) → (M' : Monoid b) →
                 (M'' : Monoid c) → (first : MonHom M M') →
                 (second : MonHom M' M'') →
               MonHom.f second (MonHom.f first (Monoid.𝑒 M)) ≡
               Monoid.𝑒 M''
id-pres-id {a} {b} {c} M M' M''
             (record { f = first ; 𝑒-preserved = refl ; ◓-preserved = ◓-preserved1 })
             (record { f = second ; 𝑒-preserved = refl ; ◓-preserved = ◓-preserved2 }) = refl


id-pres-comp : ∀ {a b c} {M : Monoid a} {M' : Monoid b}
                 {M'' : Monoid c} {f : MonHom M M'} {g : MonHom M' M''}
                 (X Y : Monoid.Underlying M) →
               MonHom.f g (MonHom.f f ((M Monoid.◓ X) Y)) ≡
               (M'' Monoid.◓ MonHom.f g (MonHom.f f X))
               (MonHom.f g (MonHom.f f Y))
id-pres-comp = ?

MonoidComp : ∀ {a b c}{M : Monoid a}{M' : Monoid b}{ M'' : Monoid c} (f : MonHom M M')
           → (g : MonHom M' M'')
           → (MonHom M M'')
MonHom.f (MonoidComp f g) = (MonHom.f g) ∘ (MonHom.f f)
MonHom.𝑒-preserved (MonoidComp {a} {b} {c} {M} {M'} {M''} f g) = id-pres-id M M' M'' f g 
MonHom.◓-preserved (MonoidComp f g) = {!!}

--zero-left-neutral : {a : ℕ} → ℕ.zero + a ≡ a
--zero-left-neutral = refl
--
--zero-right-neutral : {a : ℕ} → a + ℕ.zero ≡ a
--zero-right-neutral {ℕ.zero} = refl
--zero-right-neutral {ℕ.suc a} = cong ℕ.suc (zero-right-neutral)
--
--+-assoc : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
--+-assoc ℕ.zero b c = refl
--+-assoc (ℕ.suc a) b c = cong ℕ.suc (+-assoc a b c) 
--
--nat-mon : Monoid Level.zero
--nat-mon = record { Underlying = ℕ ;
--                  _◓_ = _+_;
--                  𝑒 = ℕ.zero;
--                  𝑒-right-neutral = zero-right-neutral;
--                  𝑒-left-neutral = zero-left-neutral;
--                  ◓-assoc  = +-assoc}
--
--
--true-left-neutral : {b : Bool} → (true ∧ b) ≡ b
--true-left-neutral = refl
--
--true-right-neutral : {b : Bool} → (b ∧ true) ≡ b
--true-right-neutral {false} = refl
--true-right-neutral {true} = refl
--
--∧-assoc : (a b c : Bool) → ((a ∧ b) ∧ c) ≡ (a ∧ (b ∧ c))
--∧-assoc false b c = refl
--∧-assoc true b c = refl
--
--
--bool-mon : Monoid Level.zero
--bool-mon = record { Underlying = Bool;
--                    _◓_ = _∧_;
--                    𝑒 = Bool.true;
--                    ◓-assoc = ∧-assoc;
--                    𝑒-left-neutral = true-left-neutral;
--                    𝑒-right-neutral = true-right-neutral}
--
--nat-to-bool : ℕ → Bool
--nat-to-bool ℕ.zero = true
--nat-to-bool (ℕ.suc x) = false

--nat2bool-op-preserve : (x y : ℕ) → ((nat-to-bool (x + y)) ≡ (nat-to-bool x) ∧ (nat-to-bool y))
--nat2bool-op-preserve ℕ.zero y = refl
--nat2bool-op-preserve (ℕ.suc x) y = refl

--nat2bool-neutral-preserve : nat-to-bool ℕ.zero ≡ true
--nat2bool-neutral-preserve = refl

--nat-to-bool-op : ∀ X Y u y
--                 → u ≡
--                 → y ≡ nat-to-bool X ∧ nat-to-bool Y
--                 → u ≡ y
--nat-to-bool-op ℕ.zero Y .(nat-to-bool Y) .(nat-to-bool Y) refl refl = refl
--nat-to-bool-op (ℕ.suc X) Y .false .false refl refl = refl


--nat-to-bool-Monoid : MonHom nat-mon bool-mon
--nat-to-bool-Monoid = record {
--                            f = nat-to-bool;
--                            𝑒-preserved = nat2bool-neutral-preserve; 
--                            ◓-preserved = nat-to-bool-op
--                            }



--id-homo : ∀ {a}{A : Monoid a} → MonHom A A
--MonHom.f (id-homo {A}) = id
--MonHom.𝑒-preserved (id-homo {A} {B}) = id-preserve _ (Monoid.𝑒 B)
--MonHom.◓-preserved (id-homo {A} {B}) = id-preserves-op (Monoid._◓_ B)

--record {
--                 f = id;                 
--                 𝑒-preserved = id-preserve;
--                 ◓-preserved = id-preserves-op
--                 }






