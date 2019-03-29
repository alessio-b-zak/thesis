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
open import Lambda hiding (count)

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

data _=λ*_ : (⊖ ⊢* ✴) → (⊖ ⊢* ✴) → Set where

  λ*-refl : ∀ {x} → x =λ* x

  λ*-sym : ∀ {x y} → x =λ* y → y =λ* x

  λ*-trans : ∀ {x y z} → x =λ* y → y =λ* z → x =λ* z

  λ*-app : ∀ {s s' t t'} → s =λ* t
        → s' =λ* t' → s ∙* t =λ* s' ∙* t'

  K-axiom : ∀ {A B} → K ∙* A ∙* B =λ* A

  S-axiom : ∀ {X Y Z}
         → S ∙* X ∙* Y ∙* Z =λ* X ∙* Z ∙* (Y ∙* Z)

  K-Ext : K =λ* (ƛ* ƛ* (K ∙* (#* 1 ∙* #* 0)))

  S-Ext : S =λ* (ƛ* ƛ* ƛ* (S ∙* #* 2 ∙* #* 1 ∙* #* 0))


ctxt-swtch : Context → λ*Context
ctxt-swtch ø = ⊖
ctxt-swtch (x , x₁) = {!!}

ni-switching : ∀ {Γ Δ} → Γ ∋ ★ → Δ ∋* ✴
ni-switching Z = {!Z*!}
ni-switching (S x) = {!!}

β→λ* : ø ⊢ ★ → ⊖ ⊢* ✴
β→λ* = {!!}
