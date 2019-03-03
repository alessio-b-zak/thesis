module Monoids where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function hiding (id)


record Monoid (a : Level) : Set (Level.suc a) where
  field
    Underlying : Set a 
    _◓_ : Underlying → Underlying → Underlying
    𝑒 : Underlying
  field
    ◓-assoc : (a b c : Underlying) → ((a ◓ b) ◓ c) ≡ (a ◓ (b ◓ c))
    𝑒-left-neutral : {a : Underlying} → 𝑒 ◓ a ≡ a
    𝑒-right-neutral : {a : Underlying} → a ◓ 𝑒 ≡ a


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
-- (g ∘ f) (X ◓ Y) ≡ ((g ∘ f) X) ◓' ((g ∘ f)
id-pres-comp {a} {b} {c} {M} {M'} {M''}
             {record { f = f1 ; 𝑒-preserved = id-pres1 ; ◓-preserved = comp-pres1 }}
             {record { f = g2 ; 𝑒-preserved = id-pres2 ; ◓-preserved = comp-pres2 }}
             X Y = case (comp-pres1 X Y) of
                        refl → ?


-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   f1 ((M Monoid.◓ X) Y) ≟ (M' Monoid.◓ f1 X) (f1 Y)
-- when checking that the pattern refl has type
-- f1 ((M Monoid.◓ X) Y) ≡ (M' Monoid.◓ f1 X) (f1 Y)


MonoidComp : ∀ {a b c}{M : Monoid a}{M' : Monoid b}{ M'' : Monoid c} (f : MonHom M M')
           → (g : MonHom M' M'')
           → (MonHom M M'')
MonHom.f (MonoidComp f g) = (MonHom.f g) ∘ (MonHom.f f)
MonHom.𝑒-preserved (MonoidComp {a} {b} {c} {M} {M'} {M''} f g) = id-pres-id M M' M'' f g 
MonHom.◓-preserved (MonoidComp f g) = {!!}
