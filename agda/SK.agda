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
open import Lambda hiding (count ; begin_ ; _∎ ; _=β⟨_⟩_ ; fin)


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

_fin?_ : (x : String) → (y : SK) → Dec (FInSK x y)
x fin? S = no {!!}
x fin? K = {!!}
x fin? (& x₁) = {!!}
x fin? (y ∙∙ y₁) = {!!}

--fin : String → SK → Bool
--fin x S = false
--fin x K = false
--fin x (& x₁) with x Str.≟ x₁
--... | yes p = true
--... | no ¬p = false
--fin x (y ∙∙ y₁) = fin x y ∨ fin x y₁

--eval : String → SK → SK
--eval x y with fin x y
--... | false = K ∙∙ y
--eval x S | true = {!!}
--eval x K | true = {!!}
--eval x (& x₁) | true = {!!}
--eval x (y ∙∙ y₁) | true = {!!}

data _=sk_ : SK → SK → Set where

  K-axiom : {X Y : SK} → K ∙∙ X ∙∙ Y =sk X

  S-axiom : {X Y Z : SK} → S ∙∙ X ∙∙ Y ∙∙ Z =sk X ∙∙ Z ∙∙ (Y ∙∙ Z)

  sk-refl : {x : SK} → x =sk x

  sk-sym : {x y : SK} → x =sk y → y =sk x

  sk-trans : {x y z : SK} → x =sk y → y =sk z → x =sk z
