module Lambda2 where


open import Data.String
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

data _⊢_ : {i : Size} → Context → Type → Set where


  `_ : ∀ {Γ A i} → Γ ∋ A →  _⊢_ {↑ i} Γ A

  ƛ_ : ∀ {Γ i} {j : Size< i} →  _⊢_ {j} (Γ , ★) ★ → _⊢_ {i} Γ ★

  _∙_ : ∀ {Γ i j} →  _⊢_ {i} Γ ★ →  _⊢_ {j} Γ ★ → _⊢_ {i ⊔ˢ j} Γ ★

  ~_ : ∀ {Γ A i} → String → _⊢_ {↑ i} Γ A

--add check for syntactic equality
count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero = Z
count {Γ , ★} (suc n) = S (count n)
count {ø} _ = ⊥-elim impossible
  where postulate impossible : ⊥


uncount : ∀ {Γ} → Γ ∋ ★ → ℕ
uncount Z = zero
uncount (S x) = suc (uncount x)

