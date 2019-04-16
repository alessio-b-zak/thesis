module Lambda2 where


open import Data.String
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Agda.Builtin.Size
open import Data.Nat
open import Data.Empty using (⊥; ⊥-elim)

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  `_
infix  8  ~_
infixl 7  _∙_


data Type : Set where
  ★ : Type

data Context : Set where
  ø : Context
  _,_ : Context → Type → Context


data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A

  ƛ_ : ∀ {Γ} → Γ , ★ ⊢ ★ → Γ ⊢ ★

  _∙_ : ∀ {Γ} → Γ ⊢ ★ → Γ ⊢ ★ → Γ ⊢ ★

  ~_ : ∀ {Γ A} → String → Γ ⊢ A
