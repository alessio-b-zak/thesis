module Combin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
open import Lambda hiding (count ; begin_ ; _∎ ; _=β⟨_⟩_)

infix  4  _⊢*_
infix  4  _∋*_
infixl 5  _,,_

infix  6  ƛ*_
infix  6  `*_
infix  8  ~*_
infixl 7  _∙*_


data λ*Type : Set where
  ✴ : λ*Type


data λ*Context : Set where
  ⊖ : λ*Context
  _,,_ : λ*Context → λ*Type → λ*Context


--max : λ*Context → λ*Context →

data _∋*_ : λ*Context → λ*Type → Set where
  Z* : ∀ {Γ A} → Γ ,, A ∋* A
  S* : ∀ {Γ A B} → Γ ∋* A → Γ ,, B ∋* A

data _⊢*_ : λ*Context → λ*Type → Set where

  `*_ : ∀ {Γ A} → Γ ∋* A → Γ ⊢* A

  ƛ*_ : ∀ {Γ} → Γ ,, ✴ ⊢* ✴ → Γ ⊢* ✴

  _∙*_ : ∀ {Γ} → Γ ⊢* ✴ → Γ ⊢* ✴ → Γ ⊢* ✴

  ~*_ : ∀ {Γ A} → String → Γ ⊢* A

  S : ∀ {Γ} → Γ ⊢* ✴

  K : ∀ {Γ} → Γ ⊢* ✴

count : ∀ {Γ} → ℕ → Γ ∋* ✴
count {Γ ,, ✴} zero = Z*
count {Γ ,, ✴} (suc n) = S* (count n)
count {⊖} _ = ⊥-elim impossible
  where postulate impossible : ⊥

#*_ : ∀ {Γ} → ℕ → Γ ⊢* ✴
#* x = `* count x

infix 2 _=λ*_
infix 1 begin_
infixr 2 _=λ⟨_⟩_
infix 3 _∎


data _=λ*_ {Γ} : (Γ ⊢* ✴) → (Γ ⊢* ✴) → Set where

  λ*-refl : ∀ {x} → x =λ* x

  λ*-sym : ∀ {x y} → x =λ* y → y =λ* x

  λ*-trans : ∀ {x y z} → x =λ* y → y =λ* z → x =λ* z

  λ*-app : ∀ {s s' t t'} → s =λ* s'
        → t =λ* t' → s ∙* t =λ* s' ∙* t'

  K-axiom : ∀ {A B} → K ∙* A ∙* B =λ* A

  S-axiom : ∀ {X Y Z}
         → S ∙* X ∙* Y ∙* Z =λ* X ∙* Z ∙* (Y ∙* Z)

  K-Ext : K =λ* (ƛ* ƛ* (K ∙* (#* 1 ∙* #* 0)))

  S-Ext : S =λ* (ƛ* ƛ* ƛ* (S ∙* #* 2 ∙* #* 1 ∙* #* 0))

  W-Ext : ∀ {M N} → M =λ* N → ƛ* M =λ* ƛ* N

  λ*-id : ƛ* #* 0 =λ* S ∙* K ∙* K

  λ*-KF : ∀ {x} → ƛ* (~* x) =λ* K ∙* (~* x)

  λ*-KB : ∀ {x} → ƛ* (`* (S* x)) =λ* K ∙* (`* x)

  λ*-KK : ƛ* K =λ* K ∙* K

  λ*-KS : ƛ* S =λ* K ∙* S

  λ*-SNI : ∀ {A B} → ƛ* (A ∙* B) =λ* S ∙* (ƛ* A) ∙* (ƛ* B)

--  λ*-KB : ∀ {Γ} {x : Γ ∋* ✴} → ƛ* (`* (S* x)) =λ* _∙*_ {?} K (`* (S* x))

begin_ : ∀ {Γ} {s t : Γ ⊢* ✴} → s =λ* t → s =λ* t
begin x = x

_∎ : ∀ {Γ} (s : Γ ⊢* ✴) → s =λ* s
_∎ _ = λ*-refl

_=λ⟨_⟩_ : ∀ {Γ} (s {t v} : Γ ⊢* ✴) → s =λ* t → t =λ* v → s =λ* v
_ =λ⟨ s=λt ⟩ t=λv = λ*-trans s=λt t=λv


id : ∀ {Γ} → Γ ⊢* ✴
id = ƛ* #* 0

id-id : ∀ {Γ} {x : Γ ⊢* ✴} → id ∙* x =λ* x
id-id {Γ} {x} = begin
              id ∙* x
            =λ⟨ λ*-app λ*-id λ*-refl ⟩
              S ∙* K ∙* K ∙* x
            =λ⟨ S-axiom ⟩
              K ∙* x ∙* (K ∙* x)
            =λ⟨ K-axiom ⟩
              x
            ∎


Free-SK : ∀ {Γ A B} {t : Γ ⊢* ✴}
       → (ƛ* A ∙* B) ∙* t =λ* (ƛ* A) ∙* t ∙* ((ƛ* B) ∙* t)
Free-SK {Γ} {A} {B} {t} =
  begin
    (ƛ* A ∙* B) ∙* t
  =λ⟨ λ*-app λ*-SNI λ*-refl ⟩
     S ∙* (ƛ* A) ∙* (ƛ* B) ∙* t
  =λ⟨ S-axiom ⟩
    (ƛ* A) ∙* t ∙* ((ƛ* B) ∙* t)
  ∎

Free-beta : ∀ {Γ x} {t : Γ ⊢* ✴} → (ƛ* (~* x)) ∙* t =λ* ~* x
Free-beta {Γ} {x} {t} =
            begin
             (ƛ* (~* x)) ∙* t
            =λ⟨ λ*-app λ*-KF λ*-refl ⟩
              K ∙* ~* x ∙* t
            =λ⟨ K-axiom ⟩
             ~* x
            ∎

Freeish-beta : ∀ {Γ x} {t : Γ ⊢* ✴} → (ƛ* (`* S* x)) ∙* t  =λ* `* x
Freeish-beta {Γ} {x} {t} =
  begin
    (ƛ* (`* S* x)) ∙* t
  =λ⟨ λ*-app λ*-KB λ*-refl ⟩
    K ∙* (`* x) ∙* t
  =λ⟨ K-axiom ⟩
    `* x
  ∎

ctxt-swtch : Context → λ*Context
ctxt-swtch ø = ⊖
ctxt-swtch (xs , ★) = ctxt-swtch xs ,, ✴

ni-sw : ∀ {Γ} → Γ ∋ ★ → (ctxt-swtch Γ) ∋* ✴
ni-sw Z = Z*
ni-sw {Γ , ★} (S x) = S* (ni-sw x)

⟦_⟧* : ∀ {Γ} → Γ ⊢ ★ → (ctxt-swtch Γ)  ⊢* ✴
⟦_⟧* (` x) = `* (ni-sw x)
⟦_⟧* {Γ} (ƛ x) = ƛ* ⟦ x ⟧*
⟦_⟧* (x ∙ y) = ⟦ x ⟧* ∙* ⟦ y ⟧*
⟦_⟧* (~ x) = ~* x


helper : ∀ {Γ} {s : Γ , ★ ⊢ ★} {t : Γ ⊢ ★}
  → (ƛ* ⟦ s ⟧*) ∙* ⟦ t ⟧* =λ* ⟦ s [ t ] ⟧*

transp : ∀ {Γ} → {x y : Γ ⊢ ★}
  → x =β y
  → ⟦ x ⟧* =λ* ⟦ y ⟧*


app-go : ∀ {Γ} {s s₁ : Γ , ★ ⊢ ★} {t : Γ ⊢ ★} →
       (ƛ* ⟦ s ⟧* ∙* ⟦ s₁ ⟧*) ∙* ⟦ t ⟧* =λ* ⟦ s [ t ] ⟧* ∙* ⟦  s₁ [ t ] ⟧*

app-go {Γ} {s} {s₁} {t}
  = begin
      (ƛ* ⟦ s ⟧* ∙* ⟦ s₁ ⟧*) ∙* ⟦ t ⟧*
    =λ⟨ Free-SK ⟩
      (ƛ* ⟦ s ⟧*) ∙* ⟦ t ⟧* ∙* ((ƛ* ⟦ s₁ ⟧*) ∙* ⟦ t ⟧*)
    =λ⟨ λ*-app helper helper ⟩
      ⟦ s [ t ] ⟧* ∙* ⟦  s₁ [ t ] ⟧*
    ∎


abs-go : ∀ {Γ} {s : Γ , ★ , ★ ⊢ ★} {t : Γ ⊢ ★} →
  (ƛ* (ƛ* ⟦ s ⟧*)) ∙* ⟦ t ⟧* =λ* ⟦ (ƛ s) [ t ] ⟧*
abs-go {.(_ , ★)} {` Z} {` Z} = begin
                                  (ƛ* (ƛ* (`* Z*))) ∙* (`* Z*)
                                =λ⟨ λ*-app (W-Ext λ*-id) λ*-refl ⟩
                                  (ƛ* (S ∙* K ∙* K)) ∙* (`* Z*)
                                =λ⟨ λ*-app λ*-SNI λ*-refl ⟩
                                  S ∙* (ƛ* S ∙* K) ∙* (ƛ* K) ∙* (`* Z*)
                                =λ⟨ S-axiom ⟩
                                  (ƛ* S ∙* K) ∙* (`* Z*) ∙* ((ƛ* K) ∙* (`* Z*))
                                =λ⟨ {!!} ⟩
                                  ƛ* (`* Z*)
                                ∎
abs-go {.(_ , _)} {` Z} {` S x} = {!!}
abs-go {Γ} {` S x} {` x₁} = {!!}
abs-go {Γ} {` Z} {ƛ t} = {!!}
abs-go {Γ} {` S x} {ƛ t} = {!!}
abs-go {Γ} {` Z} {t ∙ t₁} = {!!}
abs-go {Γ} {` S x} {t ∙ t₁} = {!!}
abs-go {Γ} {` Z} {~ x₁} = {!!}
abs-go {Γ} {` S x} {~ x₁} = {!!}
abs-go {Γ} {ƛ s} {t} = {!!}
abs-go {Γ} {s ∙ s₁} {t} = {!!}
abs-go {Γ} {~ x} {t} = {!!}

--begin
--      (ƛ* (ƛ* ⟦ s ⟧*)) ∙* ⟦ t ⟧*
--    =λ⟨ {!!} ⟩
--      ⟦ (ƛ s) [ t ] ⟧*
--    ∎

helper {Γ} {` Z} {t} = id-id
helper {Γ} {` S x} {t} = Freeish-beta
helper {Γ} {ƛ s} {t} = abs-go
helper {Γ} {s ∙ s₁} {t} = app-go
helper {Γ} {~ x} {t} = Free-beta

transp β-refl = λ*-refl
transp (β-sym x) = λ*-sym (transp x)
transp (β-trans x y) = λ*-trans (transp x) (transp y)
transp (β-app x y) = λ*-app (transp x) (transp y)
transp (β-abs x) = W-Ext (transp x)
transp β-β = helper
