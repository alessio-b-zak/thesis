module Cantor where

open import Cats.Category.Constructions.Terminal as Terminal
open import Cats.Category.Constructions.Product as Product
open import Cats.Category.Constructions.CCC as CCC
open import Data.Nat
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Cats.Category.Constructions.Exponential as Exponential
open import Cats.Category.Sets using (Sets)
open import Data.Bool using (true ; false; Bool)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Extension
open import Diagonal
import Points
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
import Cats.Category.Constructions.Unique as Unique
open import Cats.Category.Cat.Facts
open import Relation.Binary.PropositionalEquality

-- derivation of cantor's diagonal argument from lawvere's fixed pt thm

Sets1 = Sets lzero


open Terminal.Build Sets1
open Unique.Build Sets1
open Points.Build Sets1

data Pair (A : Set) (B : Set) : Set where
  mkPair : A → B → Pair A B


fst : {A B : Set} → Pair A B → A
fst (mkPair x x₁) = x

snd : {A B : Set} → Pair A B → B
snd (mkPair x x₁) = x₁

g : {X : Set} → X → ⊤
g x = ⊤.tt

tterminal :  {X : Set} {g : X → ⊤} → ⊤ → (x : X) → ⊤.tt ≡ g x
tterminal x x₁ = refl

helper :  (X : Set) → Unique.Build.∃!′
          (Sets lzero) {A = X} {B = ⊤}(λ f → ⊤)
helper X = Unique.Build.∃!-intro g _ tterminal


⊤-isTerminal : IsTerminal ⊤
⊤-isTerminal = helper


instance
  setsHasTerminal : HasTerminal (Sets1)
  setsHasTerminal = record { One = ⊤ ; isTerminal = ⊤-isTerminal}


proj-Sets1 : ∀ {A B} i → Pair A B → Bool-elim A B i
proj-Sets1 false (mkPair x x₁) = x₁
proj-Sets1 true (mkPair x x₁) = x


proj-Sets1-prf : {A B X : Set} → {x₁ : X}{i : Bool}
                 → {x : (j : Bool) → X → Bool-elim A B j}
                 → x i x₁ ≡ proj-Sets1 {A} {B} i (mkPair (x true x₁) (x false x₁))
proj-Sets1-prf {A} {B} {X} {x₁} {false} {x} = refl
proj-Sets1-prf {A} {B} {X} {x₁} {true} {x} = refl


pairPrf′ : {A B : Set} → {g : Pair A B}
        → mkPair (proj-Sets1 true g) (proj-Sets1 false g) ≡ g
pairPrf′ {A} {B} {mkPair x x₁} = refl
--with (g₁)
--... | mkPair x x₁ = refl



pairPrf : {X A B : Set} → {g : X → Pair A B} → {y : X}
        → mkPair (proj-Sets1 true (g y)) (proj-Sets1 false (g y)) ≡ g y
pairPrf {X} {A} {B} {g₁} {y} with (g₁ y)
... | mkPair x x₁ = refl


mkPair-resp : {X Y : Set} → {x x₁ : X} → {y y₁ : Y}
            → (x ≡ x₁) → (y ≡ y₁) → mkPair x y ≡ mkPair x₁ y₁
mkPair-resp {X} {Y} {x} {.x} {y} {.y} refl refl = refl

isProdHelp′ :  {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
           {g : Pair A B} →
         (∀ i (x₁ : X) → x i x₁ ≡ proj-Sets1 i (g)) →
         (x₁ : X) → mkPair (x true x₁) (x false x₁) ≡ g
isProdHelp′ {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q = trans (mkPair-resp p q) (pairPrf′ {A} {B})


isProdHelp :  {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
           {g₁ : X → Pair A B} →
         (∀ i (x₁ : X) → x i x₁ ≡ proj-Sets1 i (g₁ x₁)) →
         (x₁ : X) → mkPair (x true x₁) (x false x₁) ≡ g₁ x₁
isProdHelp {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q  = trans (mkPair-resp p q) (pairPrf {X} {A} {B} {g₁})


instance
  setsHasBinaryProducts : HasBinaryProducts (Sets1)
  setsHasBinaryProducts
    = record { _×′_ = λ A B →
                     record { prod = Pair A B ;
                              proj = proj-Sets1 ;
                              isProduct = λ x → Unique.Build.∃!-intro
                                            (λ x₁ → mkPair (x true x₁) (x false x₁))
                                            (λ i x₁ → proj-Sets1-prf {A} {B} {_} {x₁} {i} {x})
                                            λ x₁ x₂ → isProdHelp x₁ x₂ }
                            }

-- TODO: show pt surjective ⇒ surjective

sets1Eval : ∀ {B C} → Pair (B → C) B → C
sets1Eval (mkPair x x₁) = x x₁


sets1Curry : {A B C : Set} → (Pair A B → C) → (A → B → C)
sets1Curry x x₁ x₂ = x (mkPair x₁ x₂)

open ≡-Reasoning


-- Postulate extensionality perhaps not necessary
postulate
  ext : Extensionality lzero lzero


go : {B C A : Set} {f : Pair A B → C} {g₁ : A → B → C} →
     ((x : Pair A B) → g₁ (proj-Sets1 true x) (proj-Sets1 false x) ≡ f x)
     → (x : A) → (λ x₂ → f (mkPair x x₂)) ≡ g₁ x
go {B} {C} {A} {f} {g₁} x x₁
  = let boom = λ a → sym (x (mkPair x₁ a))
        foo = ext x
        foo′ = ext boom
    in foo′

instance
  setsHasExponentials : HasExponentials Sets1
  setsHasExponentials = record { _↝′_
                        = λ B C → record { Cᴮ = B → C ;
                                           eval = sets1Eval ;
                                           curry′ = λ f →
                                             Unique.Build.∃!-intro (sets1Curry f)
                                                                   (λ x → cong f pairPrf′)
                                                                   go }}


instance
  setsHasFiniteProducts : HasFiniteProducts Sets1
  setsHasFiniteProducts = record {}

instance
  setsHasIsCCC : IsCCC Sets1
  setsHasIsCCC = record {}


not : Bool → Bool
not false = true
not true = false



not-fx-pt : ∀ {x} → (not x) ≢ x
not-fx-pt {false} ()
not-fx-pt {true} ()

bool-no-fix-pt : {X : ⊤ → Bool} → not (X ⊤.tt) ≡ X ⊤.tt → ⊥
bool-no-fix-pt x = not-fx-pt x

noFixPtBool : ¬ FixedPointProperty Bool
noFixPtBool x with (x not)
... | record { X = X ; isFixedPoint = isFixedPoint } = contradiction (isFixedPoint ⊤.tt) bool-no-fix-pt

open HasExponentials setsHasExponentials
open Diagonal

cantorsDiagonalTheorem : ¬ PointSurjective ℕ (ℕ ↝ Bool)
cantorsDiagonalTheorem = cantor Sets1 noFixPtBool

-- show that (A ↝ Bool) ≅ membership question on A
