module Lambda where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)

open import Data.String
open import Data.Product hiding (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Data.Sum
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

--if doesn't work take away proof bigger than ℕ as only will be used for lambdaterms
data NotMatchVar {B} : (Γ : Context) → ℕ → Γ ∋ B → Set where
  zms : ∀ {Γ x} → NotMatchVar {B} (Γ , B) (suc x) Z
  smz : ∀ {Γ A} → {x : Γ ∋ B} → NotMatchVar {B} (Γ , A) zero (S x)
  sms : ∀ {Γ x y A} → NotMatchVar Γ x y → NotMatchVar {B} (Γ , A) (suc x) (S y)

¬zmz : ∀ {B Γ} → NotMatchVar (Γ , B) 0 Z → ⊥
¬zmz ()


¬sms : ∀ {Γ B B₁ x} {y : Γ ∋ B} → ¬ NotMatchVar Γ x y → NotMatchVar (Γ , B₁) (suc x) (S y) → ⊥
¬sms x₁ (sms x) = x₁ x


_mv?_ : ∀ {Γ B} → (x : ℕ) → (y : Γ ∋ B)  → Dec (NotMatchVar Γ x y)
_mv?_ {.(_ , B)} {B} zero Z = no ¬zmz
_mv?_ {.(_ , B)} {B} (suc x) Z = yes zms
_mv?_ {.(_ , _)} {B} zero (S y) = yes smz
_mv?_ {.(_ , _)} {B} (suc x) (S y) with (x mv? y)
... | yes p = yes (sms p)
... | no ¬p = no (¬sms ¬p)


data ¬FIn {Γ} : ℕ → Γ ⊢ ★ → Set where

  xin~ : ∀ {n x} → ¬FIn n (~ x)

  xinx : ∀ {n x} → NotMatchVar Γ n x → ¬FIn {Γ} n (` x)

  xinλ : ∀ {n x} → ¬FIn (suc n) x → ¬FIn n (ƛ x)

  xin∙ : ∀ {n x y} → (¬FIn n x) × (¬FIn n y) → ¬FIn n (x ∙ y)


¬xinx : ∀ {Γ x} {x₁ : Γ ∋ ★} → ¬ NotMatchVar Γ x x₁ → ¬FIn x (` x₁) → ⊥
¬xinx x₂ (xinx x₃) = x₂ x₃


¬xinλ : ∀ {Γ x} {y : Γ , ★ ⊢ ★} → ¬ ¬FIn (suc x) y → ¬FIn x (ƛ y) → ⊥
¬xinλ x₁ (xinλ x) = x₁ x


¬xin∙ : ∀ {Γ x} {y y₁ : Γ ⊢ ★} → ¬ ¬FIn x y → ¬FIn x (y ∙ y₁) → ⊥
¬xin∙ x₁ (xin∙ ⟨ fst , snd ⟩) = x₁ fst

¬xin∙` : ∀ {Γ x} {y₁ y : Γ ⊢ ★} → ¬ ¬FIn x y₁ → ¬FIn x (y ∙ y₁) → ⊥
¬xin∙` x₁ (xin∙ ⟨ fst , snd ⟩) = x₁ snd


_fi?_ : ∀ {Γ} → (x : ℕ) → (y : Γ ⊢ ★) → Dec (¬FIn x y)
x fi? (` x₁) with (x mv? x₁)
... | yes p = yes (xinx p)
... | no ¬p = no (¬xinx ¬p)
x fi? (ƛ y) with ((suc x) fi? y)
... | yes p = yes (xinλ p)
... | no ¬p = no (¬xinλ ¬p)
x fi? (y ∙ y₁) with (x fi? y)
... | no ¬p = no (¬xin∙ ¬p)
... | yes p with (x fi? y₁)
...        | yes p₁ = yes (xin∙ ⟨ p , p₁ ⟩)
...        | no ¬p = no (¬xin∙` ¬p)
x fi? (~ x₁) = yes xin~


reduceContxt : ℕ → Context → Context
reduceContxt zero x₁ = x₁
reduceContxt (suc x) ø = ø
reduceContxt (suc x) (y , x₁) = reduceContxt x y


data ConxtSize : ℕ → Context → Set where
  1mz : ConxtSize 0 ( ø , ★ )
  sucms : ∀ {Γ x} → ConxtSize x Γ → ConxtSize (suc x) (Γ , ★)


fuck : ∀ {Γ x} → (t : Γ , ★ ⊢ ★) → ConxtSize x Γ → (¬FIn x t) → (Γ ⊢ ★) 
fuck {ø} {zero} (~ x) x₁ xin~ = ~ x
fuck {ø} {zero} .(` S _) () (xinx smz)
fuck {ø} {zero} .(ƛ _) () (xinλ x)
fuck {ø} {zero} .(_ ∙ _) () (xin∙ x₂)
fuck {.ø , .★} {zero} (` Z) 1mz (xinx ())
fuck {.ø , .★} {zero} (` S x) 1mz (xinx y) = ` x
fuck {.ø , .★} {zero} (ƛ t) 1mz (xinλ x) with (fuck t (sucms 1mz) x)
... | p = ƛ p
fuck {.ø , .★} {zero} (t ∙ t₁) 1mz (xin∙ ⟨ fst , snd ⟩) = (fuck t 1mz fst) ∙ (fuck t₁ 1mz snd)
fuck {.ø , .★} {zero} (~ x) 1mz xin~ = ~ x
fuck {ø} {suc x} t x₁ x₂ = {!!}
fuck {y , x₃} {suc x} t x₁ x₂ = {!!}

-- all this could be avoided by using contexts as Fin
--add size datatype
--add reduce datatype size
tester : (x : ø , ★ ⊢ ★) → ¬FIn 0 x → ø ⊢ ★
tester (` Z) (xinx ())
tester (` S ()) y
tester (ƛ x) (xinλ y) = {!!}
tester (x ∙ x₁) (xin∙ ⟨ fst , snd ⟩) = ( tester x fst ) ∙ ( tester x₁ snd )
tester (~ x) y₁ = ~ x



#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# x = ` count x


-- 1st case when B = A
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
   → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)


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


LambdaTerm : Set
LambdaTerm = ø ⊢ ★


x : LambdaTerm
x = ƛ ƛ ƛ (# 0 ∙ # 1)
