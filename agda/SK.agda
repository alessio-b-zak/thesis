module SK where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String
open import Data.String.Unsafe as Str
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Unit using (⊤; tt)
open import Data.Sum
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Lambda hiding (count ; begin_ ; _∎ ; _=β⟨_⟩_)


--if you use closed contexts all free vars will be metavars
--introduce a method of checking for presence of vars.


--todo eval,
infixl 7 _∙∙_
infix 8 &_

data SK : Set where

  S : SK

  K : SK

  &_ : String → SK

  _∙∙_ : SK → SK → SK

infix 2 _=sk_

data FInSK : String → SK → Set where

  fIn& : {x : String} → FInSK x (& x)

  fIn∙∙ : ∀ {x y z} → (FInSK z x) ⊎ (FInSK z y) → FInSK z (x ∙∙ y)


¬finS : ∀ {x} → ¬ FInSK x S
¬finS ()


¬finK : ∀ {x} → ¬ FInSK x K
¬finK ()

¬fin& : ∀ {x x₁} → ¬ x ≡ x₁  → ¬ FInSK x (& x₁)
¬fin& x₂ fIn& = x₂ refl

¬fin∙∙ : ∀ {x y z} → ¬ FInSK z x →  ¬ FInSK z y → ¬ FInSK z (x ∙∙ y)
¬fin∙∙ x₁ x₂ (fIn∙∙ (inj₁ x)) = x₁ x
¬fin∙∙ x₁ x₂ (fIn∙∙ (inj₂ y)) = x₂ y

_fin?_ : (x : String) → (y : SK) → Dec (FInSK x y)
x fin? S = no ¬finS
x fin? K = no ¬finK
x fin? (& x₁) with x ≟ x₁
... | yes refl = yes fIn&
... | no ¬p = no (¬fin& ¬p)
x fin? (y ∙∙ y₁) with (x fin? y)
... | yes p = yes  (fIn∙∙ (inj₁ p))
... | no ¬p with (x fin? y₁)
...             | yes p = yes (fIn∙∙ (inj₂ p ))
...             | no ¬p₁ = no (¬fin∙∙ ¬p ¬p₁)


eval : String → SK → SK
eval x y with (x fin? y)
eval x S | yes ()
eval x K | yes ()
eval x (& x₁) | yes p = S ∙∙ K ∙∙ K
eval x (y ∙∙ y₁) | yes p = S ∙∙ (eval x y) ∙∙ (eval x y₁)
eval x S | no ¬p = K ∙∙ S
eval x K | no ¬p = K ∙∙ K
eval x (& x₁) | no ¬p = K ∙∙ (& x₁)
eval x (y ∙∙ y₁) | no ¬p = K ∙∙ (y ∙∙ y₁)



data _=sk_ : SK → SK → Set where

  K-axiom : {X Y : SK} → K ∙∙ X ∙∙ Y =sk X

  S-axiom : {X Y Z : SK} → S ∙∙ X ∙∙ Y ∙∙ Z =sk X ∙∙ Z ∙∙ (Y ∙∙ Z)

  sk-refl : {x : SK} → x =sk x

  sk-sym : {x y : SK} → x =sk y → y =sk x

  sk-trans : {x y z : SK} → x =sk y → y =sk z → x =sk z

  W-Ext : ∀ {x y} → x =sk eval y x

  K-Ext : ∀ {x y} → K =sk eval x (eval y (K ∙∙ (& x) ∙∙ (& y)))

  S-Ext : ∀ {x y z} → S =sk eval x (eval y ( eval z (S ∙∙ (& x) ∙∙ (& y) ∙∙ (& z)) ))


--two functions one that takes empty context extended and next
--if var does not appear can reduce context

--evalNum x y with (x fi? y)
--evalNum x .(` _) | yes (xinx x₂) = S ∙∙ K ∙∙ K
--evalNum x (ƛ t) | yes (xinλ p) = evalNum (suc x) t
--evalNum x (c ∙ d) | yes (xin∙ x₂) = S ∙∙ (evalNum x c) ∙∙ (evalNum x d)
--evalNum x y | no p =  {!K ∙∙ (convert y) !}


convert : LambdaTerm → SK
convert (` ())
convert (ƛ x) = {!!}
convert (x ∙ x₁) = convert x ∙∙ convert x₁
convert (~ x) = & x
