module Monoids where

open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Function hiding (id)

record Monoid (a : Level) : Set (lsuc a) where
  field
    A : Set a
    _∙_ : A → A → A
    e : A
  field
    ∙-assoc : (a b c : A) → ((a ∙ b) ∙ c) ≡ (a ∙ (b ∙ c))
    e-left-neutral : {a : A} → e ∙ a ≡ a
    e-right-neutral : {a : A} → a ∙ e ≡ a



--id : ∀ {a} {A : Set a} → A → A
--id x = x
--
--idcomp : ∀ {a}{b} {A : Set a}{B : Set b} {X : A}(f : A → B) → id (f X) ≡ f X
--idcomp f = refl
--

record MonHom {L L'} (M : Monoid L) (M' : Monoid L') : Set ( L ⊔ L') where
  open Monoid M
  open Monoid M' renaming ( e to e'; _∙_ to _∙'_ ; A to A')
  field
    f : A → A'
    𝑒-preserved : f e ≡ e'
    ◓-preserved : (X Y : A) → (f (X ∙ Y)) ≡ (f X ∙' f Y)


-- open Monoid
-- 
-- id-pres-id : ∀ {a b c} → (M : Monoid a) → (M' : Monoid b) →
--                  (M'' : Monoid c) → (first : MonHom M M') →
--                  (second : MonHom M' M'') →
--                MonHom.f second (MonHom.f first (Monoid.𝑒 M)) ≡
--                Monoid.𝑒 M''
-- id-pres-id {a} {b} {c} M M' M''
--              (record { f = first ; 𝑒-preserved = refl ; ◓-preserved = ◓-preserved1 })
--              (record { f = second ; 𝑒-preserved = refl ; ◓-preserved = ◓-preserved2 }) = refl
-- 
-- id-compose-neutral : ∀{a b}{A : Set a}{B : Set b}(x : A)(f : A → B) → id (f x) ≡ f x
-- id-compose-neutral x f = refl
-- 
-- 
-- bar : ∀ {a b}
--       → (M : Monoid a)
--       → (M' : Monoid b)
--       → (first : MonHom M M')
--       → id (MonHom.f first (Monoid.𝑒 M)) ≡ Monoid.𝑒 M'
-- bar M M' record { f = kek ; 𝑒-preserved = 𝑒-preserved ; ◓-preserved = ◓-preserved } = 
--   let b = (id-compose-neutral (Monoid.𝑒 M) kek)
--   in  trans b 𝑒-preserved
-- 
-- 
-- id-pres-comp : ∀ {a b c} (M : Monoid a) (M' : Monoid b)
--                  (M'' : Monoid c) (f : MonHom M M') (g : MonHom M' M'')
--                  (X Y : Monoid.Underlying M) →
--                MonHom.f g (MonHom.f f ((M Monoid.◓ X) Y)) ≡
--                (M'' Monoid.◓ MonHom.f g (MonHom.f f X))
--                (MonHom.f g (MonHom.f f Y))
-- -- (g ∘ f) (X ◓ Y) ≡ ((g ∘ f) X) ◓' ((g ∘ f)
-- id-pres-comp {a} {b} {c} M M' M''
--              (record { f = f1 ; 𝑒-preserved = id-pres1 ; ◓-preserved = comp-pres1 })
--              (record { f = g2 ; 𝑒-preserved = id-pres2 ; ◓-preserved = comp-pres2 })
--              X Y  = let
--                id-pres1 = (comp-pres1 X Y)
--                f1X = f1 X
--                f2Y = f1 Y
--                g2ap-id-pres1 = cong g2 id-pres1
--                id-pres2 = (comp-pres2 f1X f2Y)
--                in trans g2ap-id-pres1 id-pres2 
-- 
-- 
-- MonoidComp : ∀ {a b c}{M : Monoid a}{M' : Monoid b}{ M'' : Monoid c} (g : MonHom M' M'')
--            → (f : MonHom M M')
--            → (MonHom M M'')
-- MonHom.f (MonoidComp g f) = (MonHom.f g) ∘ (MonHom.f f)
-- MonHom.𝑒-preserved (MonoidComp {a} {b} {c} {M} {M'} {M''} g f) = id-pres-id M M' M'' f g 
-- MonHom.◓-preserved (MonoidComp {a} {b} {c} {M} {M'} {M''} g f) = id-pres-comp M M' M'' f g
-- 
-- 
-- id-preserve : ∀ {a}(A : Set a) → (x : A) → (id x) ≡ x
-- id-preserve A x = refl
-- 
-- id-preserves-op : ∀ {a}{G : Set a} (_∘_ : G → G → G)(A B : G)  → id (A ∘ B) ≡ (id A) ∘ (id B)
-- id-preserves-op {a} {G} _∘_ A B  = refl
-- 
-- 
-- id-homo : ∀ {a}{A : Monoid a} → MonHom A A
-- MonHom.f (id-homo {A}) = Function.id
-- MonHom.𝑒-preserved (id-homo {A} {B}) = id-preserve _ (Monoid.𝑒 B)
-- MonHom.◓-preserved (id-homo {A} {B}) = id-preserves-op (Monoid._◓_ B)
-- 
-- 
-- --thing : ∀ {a b}{A : Monoid a}{B : Monoid b}(first : MonHom A B) → MonHom.f (MonoidComp id-homo first) ≡ MonHom.f first 
-- --thing first = refl
-- --
-- --thing' : ∀ {a b}{A : Monoid a}{B : Monoid b}(first : MonHom A B) → MonHom.𝑒-preserved (MonoidComp id-homo first) ≡ MonHom.𝑒-preserved first
-- --thing' {a} {b} {A} {B} first with (id-pres-id A B B first id-homo)
-- --thing' {a} {b} {A} {B} record { f = f ; 𝑒-preserved = 𝑒-preserved ; ◓-preserved = ◓-preserved } | p = {!!}
-- 
-- MonHom-Intro : ∀ {a b}(M : Monoid a)(M' : Monoid b){A B : Underlying M}
--                {f f' : (Underlying M) → (Underlying M')}
--                {s : f (𝑒 M) ≡ 𝑒 M'}
--                → {s' : f' (𝑒 M) ≡ 𝑒 M'}
--                → (fp : f ≡ f')
--                → subst (λ f → (f (𝑒 M) ≡ (𝑒 M'))) fp s ≡ s'
--                → (x : ((X Y : Underlying M) → f ((_◓_ M) X Y) ≡ (_◓_ M')(f X) (f Y)))
--                → (x' : ((X Y : Underlying M) → f' ((_◓_ M) X Y) ≡ (_◓_ M') (f' X) (f' Y)))
--                → subst (λ g → ((X Y : Underlying M) → g ((_◓_ M) X Y) ≡ (_◓_ M') (g X) (g Y))) fp x ≡ x'
--                → (Monny {a} {b} {M} {M'} f s x) ≡ (Monny f' s' x')
-- MonHom-Intro M M' refl refl y .y refl = refl
-- 
-- monhom-left-neutral : ∀ {a} (A B : Monoid a) (first : MonHom A B) →
--                       MonoidComp id-homo first ≡ first
-- monhom-left-neutral A B first with (MonoidComp id-homo first)
-- ... | p = {!!}
-- 
-- --record Monoid ℓ ℓ≈ : Set (lsuc (ℓ ⊔ ℓ≈)) where
-- --
-- --  field
-- --    Underlying : Set ℓ
-- --    ≈ : Rel Underlying ℓ≈
-- --    ≈-equiv : IsEquivalence ≈
-- --
-- --    _◓_ : Underlying → Underlying → Underlying
-- --    𝑒 : Underlying
-- --    
-- --    ◓-resp : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ◓ b) ≈ (a′ ◓ b′)
-- --    ◓-assoc : (a b c : Underlying) → ((a ◓ b) ◓ c) ≡ (a ◓ (b ◓ c))
-- --    𝑒-left-neutral : {a : Underlying} → 𝑒 ◓ a ≡ a
-- --    𝑒-right-neutral : {a : Underlying} → a ◓ 𝑒 ≡ a
