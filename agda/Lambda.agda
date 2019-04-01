module Lambda where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)

open import Data.String
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)


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

--add check for syntactic equality
count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero = Z
count {Γ , ★} (suc n) = S (count n)
count {ø} _ = ⊥-elim impossible
  where postulate impossible : ⊥


uncount : ∀ {Γ} → Γ ∋ ★ → ℕ
uncount Z = zero
uncount (S x) = suc (uncount x)


data MatchVar {B} : (Γ : Context) → ℕ → Γ ∋ B → Set where
  zmz : ∀ {Γ} → MatchVar {B} (Γ , B) zero Z
  sms : ∀ {Γ B x y} → MatchVar Γ x y → MatchVar (Γ , B) (suc x) (S y)


¬zmvs : ∀ {Γ B} {y : Γ ∋ ★} → ¬ MatchVar (Γ , B) zero (S y)
¬zmvs ()

¬smvz : ∀ {Γ x} → ¬ MatchVar (Γ , ★) (suc x) Z
¬smvz ()

¬smvs : ∀ {Γ x} {y : Γ ∋ ★} {B} → ¬ MatchVar Γ x y → ¬ MatchVar (Γ , B) (suc x) (S y)
¬smvs x₁ (sms x) = x₁ x


_mv?_ : ∀ {Γ} → (x : ℕ) → (y : Γ ∋ ★) → Dec (MatchVar Γ x y)
_mv?_ {.(_ , ★)} zero Z = yes zmz
_mv?_ {.(_ , _)} zero (S y) = no ¬zmvs
_mv?_ {.(_ , ★)} (suc x) Z = no ¬smvz
_mv?_ {.(_ , _)} (suc x) (S y) with x mv? y
... | yes p = yes (sms p)
... | no ¬p = no (¬smvs ¬p)

--
--data FIn {Γ} : ℕ → Γ ⊢ ★ → Set where
--
--  xinx : ∀ {n x} → MatchVar Γ n x  → FIn {Γ} n (` x)
--
--  xinλ : ∀ {n x} → FIn (suc n) x → FIn n (ƛ x)
--
--  xin∙ : ∀ {n x y} → FIn n x → FIn n y → FIn n (x ∙ y)
--
--
--_fi?_ : ∀ {Γ} → (x : ℕ) → (y : Γ ⊢ ★) → Dec (FIn x y)
--x fi? (` x₁)  with x mv? x₁
--... | yes p = yes (xinx p)
--... | no ¬p = {!!}
--x fi? (ƛ y) = {!!}
--x fi? (y ∙ y₁) = {!!}
--x fi? (~ x₁) = {!!}

#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# x = ` count x

-- 1st case when B = A
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
   → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--zzzz : FIn {ø , ★} 0 (ƛ # 1)
--zzzz = xinλ (xinx (sms zmz))



rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
      → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ y) = ƛ rename (ext ρ) y
rename ρ (L ∙ M) = rename ρ L ∙ rename ρ M
rename ρ (~ x) = ~ x

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S x) = rename S (σ x)

subst : ∀ {Γ Δ}
     → (∀ {A} → Γ ∋ A → Δ ⊢ A)
     → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ x) = ƛ subst (exts σ) x
subst σ (x ∙ x₁) = (subst σ x) ∙ (subst σ x₁)
subst σ (~ x) = ~ x

_[_] : ∀ {Γ A B}
    → Γ , B ⊢ A
    → Γ ⊢ B
    → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z = M
    σ (S x) = ` x


infix 2 _=β_
infix 1 begin_
infixr 2 _=β⟨_⟩_
infix 3 _∎


data _=β_ {Γ} : (Γ ⊢ ★) → (Γ ⊢ ★) → Set where

  β-refl : ∀ {x} → x =β x

  β-sym : ∀ {x y} → x =β y → y =β x

  β-trans : ∀ {x y z} → x =β y → y =β z
         → x =β z

  β-app : ∀ {s s' t t'} → s =β s' → t =β t'
       → s ∙ t =β s' ∙ t'

  β-abs : ∀ {s t} → s =β t → ƛ s =β ƛ t

  β-β : ∀ {s t} → (ƛ s) ∙ t =β s [ t ]



begin_ : ∀ {Γ} {s t : Γ ⊢ ★} → s =β t → s =β t
begin x = x

_∎ : ∀ {Γ} (s : Γ ⊢ ★) → s =β s
_∎ _ = β-refl

_=β⟨_⟩_ : ∀ {Γ} (s {t v} : Γ ⊢ ★) → s =β t → t =β v → s =β v
_ =β⟨ s=βt ⟩ t=βv = β-trans s=βt t=βv

fin : ∀ {Γ} → (x : ℕ) → (y : Γ ⊢ ★) → Bool
fin x (` x₁) with x mv? x₁
... | yes p = true
... | no ¬p = false
fin x (ƛ y) = fin (suc x) y
fin x (y ∙ y₁) = fin x y ∨ fin x y₁
fin x (~ x₁) = false

LambdaTerm : Set
LambdaTerm = ø ⊢ ★
