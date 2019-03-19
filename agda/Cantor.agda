module Cantor where

open import Cats.Category.Constructions.Terminal as Terminal
open import Cats.Category.Constructions.Product as Product
open import Cats.Category.Sets using (Sets)
open import Data.Bool using (true ; false; Bool)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Extension
open import Diagonal
open import Data.Unit.Base using (⊤)
import Cats.Category.Constructions.Unique as Unique
open import Cats.Category.Cat.Facts
open import Relation.Binary.PropositionalEquality

-- derivation of cantor's diagonal argument from lawvere's fixed pt thm

Sets1 = Sets lzero


open Terminal.Build Sets1
open Unique.Build Sets1


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


isProdHelp :  {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
           {g₁ : X → Pair A B} →
         (∀ i (x₁ : X) → x i x₁ ≡ proj-Sets1 i (g₁ x₁)) →
         (x₁ : X) → mkPair (x true x₁) (x false x₁) ≡ g₁ x₁
isProdHelp x y with (x true y) | (x false y)
... | p | q  = {!!}



instance
  setsHasBinaryProducts : HasBinaryProducts (Sets1)
  setsHasBinaryProducts
    = record { _×′_ = λ A B →
                     record { prod = Pair A B ;
                              proj = proj-Sets1 ;
                              isProduct = λ x → Unique.Build.∃!-intro
                                            (λ x₁ → mkPair (x true x₁) (x false x₁))
                                            (λ i x₁ → proj-Sets1-prf {A} {B} {_} {x₁} {i} {x})
                                            {!!} }
                            }
  
