\documentclass[a4paper, 12pt]{article}
\usepackage{agda}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{autofe}

\date{}

\title{Thesis}

\begin{document}
\maketitle

\begin{code}
module ThesisCantor where

open import Cats.Category.Constructions.Terminal as Terminal
open import Cats.Category.Constructions.Product as Product
open import Cats.Util.Function as Function using (_∘_)
open import Cats.Category.Constructions.CCC as CCC
open import Data.Nat
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Cats.Category.Constructions.Exponential as Exponential
open import Cats.Category.Sets using (Sets)
open import Data.Bool using (true ; false; Bool)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation hiding (contradiction)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Extension
open import Diagonal
import Points
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤)
import Cats.Category.Constructions.Unique as Unique
open import Cats.Category.Cat.Facts
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

-- derivation of cantor's diagonal argument from lawvere's fixed pt thm
\end{code}



%<*cantor-univ>
\begin{code}
Sets1 = Sets lzero
\end{code}
%</cantor-univ>

\begin{code}
open Terminal.Build Sets1 hiding (terminal-unique)
open Unique.Build Sets1
open Points.Build Sets1
open Product.Build Sets1
\end{code}

%<*cantor-pair>
\begin{code}
data Pair (A : Set) (B : Set) : Set where
  mkPair : A → B → Pair A B
\end{code}
%</cantor-pair>



%\begin{code}
%proj-uniqueness : ∀ {X} (A B : Set) (p : ∀ i → X → Bool-elim A B i) →
%                ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
%\end{code}

%<*sets-proj>
\begin{code}
proj-pair : ∀ {A B} i → Pair A B → Bool-elim A B i
proj-pair false (mkPair x x₁) = x₁
proj-pair true (mkPair x x₁) = x
\end{code}
%</sets-proj>

\begin{code}
fst : ∀ {A B} → Pair A B → A
fst = proj-pair true
\end{code}

\begin{code}
snd : ∀ {A B} → Pair A B → B
snd = proj-pair false
\end{code}

%<*cantor-proj-sat>
\begin{code}
proj-sat-univ : {A B X : Set} → {x₁ : X}{i : Bool}
  → {x : (j : Bool) → X → Bool-elim A B j}
  → x i x₁ ≡ proj-pair {A} {B} i (mkPair (x true x₁) (x false x₁))
\end{code}
%</cantor-proj-sat>

\begin{code}
proj-sat-univ {A} {B} {X} {x₁} {false} {x} = refl
proj-sat-univ {A} {B} {X} {x₁} {true} {x} = refl

\end{code}

\begin{code}
pairPrf : {X A B : Set} → {g : X → Pair A B} → {y : X}
  → mkPair (proj-pair true (g y)) (proj-pair false (g y)) ≡ g y
pairPrf {X} {A} {B} {g₁} {y} with (g₁ y)
... | mkPair x x₁ = refl

\end{code}

\begin{code}
pairPrf′ : {A B : Set} → {g : Pair A B}
  → mkPair (proj-pair true g) (proj-pair false g) ≡ g
pairPrf′ {A} {B} {mkPair x x₁} = refl
\end{code}

%\begin{code}
%proj-uniqueness A B p =
%  let v = λ x → mkPair (p true x) (p false x)
%  in Unique.Build.∃!-intro v (λ i b → proj-pair-prf {A} {{!B!}} {_} {b} {{!!}} {{!!}} ) {!!}
%\end{code}

\begin{code}
mkPair-resp : {X Y : Set} → {x x₁ : X} → {y y₁ : Y}
  → (x ≡ x₁) → (y ≡ y₁) → mkPair x y ≡ mkPair x₁ y₁
mkPair-resp {X} {Y} {x} {.x} {y} {.y} refl refl = refl

\end{code}



%<*cantor-unique>
\begin{code}
proj-unique''' : {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
              {g : X → Pair A B} →
              (∀ i (x₁ : X) → x i x₁ ≡ proj-pair i (g x₁)) →
              (x₁ : X) →
              mkPair (x true x₁) (x false x₁) ≡ g x₁
\end{code}
%</cantor-unique>

\begin{code}
proj-unique : {A B X : Set} {x : ∀ i → X → Bool-elim A B i}
               {g : X → Pair A B} →
               (h : ∀ i (x₁ : X) → x i x₁ ≡ proj-pair i (g x₁)) →
               (x₁ : X) → mkPair (x true x₁) (x false x₁) ≡ g x₁
proj-unique {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q = trans {!!} {!!}
\end{code}

\begin{code}
proj-unique''' {A} {B} {X} {x₁} {g₁} x y with (x true y) | (x false y)
... | p | q  = trans (mkPair-resp p q) (pairPrf {X} {A} {B} {g₁})
\end{code}

%<*cantor-unique-type>
\begin{code}
proj-uniqueness : ∀ {A B X} (p : ∀ i → X → Bool-elim A B i) →
  ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
\end{code}
%</cantor-unique-type>

%<*cantor-unique-def>
\begin{code}
proj-uniqueness {A} {B} = λ p →
  let u = (λ x → mkPair (p true x) (p false x))
  in Unique.Build.∃!-intro u {!!} {!!}
\end{code}
%</cantor-unique-def>

\begin{code}
proj-uniqueness' : ∀ {A B X} (p : ∀ i → X → Bool-elim A B i) →
  ∃![ u ] ( ∀ i (b : X) → p i b ≡ proj-pair i (u b))
proj-uniqueness' {A} {B} = λ p →
  let u = (λ x → mkPair (p true x) (p false x))
  in
\end{code}

%<*cantor-unique-def1>
\begin{code}
   Unique.Build.∃!-intro
    u
    (λ i b → proj-sat-univ {A} {B} {_} {b} {i} {p})
    {!!}
\end{code}
%</cantor-unique-def1>


%<*sets-product>
\begin{code}
set-product : {A B : Set} → BinaryProduct A B
set-product {A} {B} = record { prod = Pair A B ; proj = proj-pair ; isProduct = {!!} }
\end{code}
%</sets-product>

\begin{code}
instance
  setsHasBinaryProducts : HasBinaryProducts (Sets1)
  setsHasBinaryProducts
    = record { _×′_ = λ A B →
             record { prod = Pair A B ;
                      proj = proj-pair ;
                      isProduct = proj-uniqueness }}
\end{code}

%= record { _×′_ = λ A B →
%record { prod = Pair A B ;
%proj = proj-pair ;
%isProduct = proj-uniqueness A B}
%}



%<*cantor-terminal-arrow>
\begin{code}
terminal-arrow : {X : Set} → X → ⊤
terminal-arrow x = ⊤.tt
\end{code}
%</cantor-terminal-arrow>

%<*cantor-terminal-unique>
\begin{code}
terminal-unique :  {X : Set} {g : X → ⊤} → ⊤ → (x : X) → ⊤.tt ≡ g x
terminal-unique x x₁ = refl
\end{code}
%</cantor-terminal-unique>

%<*cantor-terminal-prop1>
\begin{code}
terminal-property :  (X : Set) → ∃! X ⊤
terminal-property X =
  Unique.Build.∃!-intro {!!} _ {!!}
\end{code}
%</cantor-terminal-prop1>

\begin{code}
terminal-property' :  (X : Set) → ∃! X ⊤
terminal-property' X = Unique.Build.∃!-intro terminal-arrow _ {!!}
\end{code}

\begin{code}
terminal-property'' :  (X : Set) → ∃! X ⊤
terminal-property'' X =
\end{code}
%<*cantor-terminal-prop2>
\begin{code}
  Unique.Build.∃!-intro terminal-arrow _ terminal-unique
\end{code}
%</cantor-terminal-prop2>

%<*cantor-tisterminal>
\begin{code}
⊤-isTerminal : IsTerminal ⊤
⊤-isTerminal = terminal-property
\end{code}
%</cantor-tisterminal>


\begin{code}
instance
  setsHasTerminal : HasTerminal (Sets1)
  setsHasTerminal = record { One = ⊤ ; isTerminal = ⊤-isTerminal}
\end{code}

\begin{code}
open Exponential.Build Sets1
\end{code}

%<*cantor-eval>
\begin{code}
set-eval : ∀ {B C} → Pair (B → C) B → C
set-eval (mkPair f x) = f x
\end{code}
%</cantor-eval>

\begin{code}

\end{code}

%<*cantor-curry>
\begin{code}
sets-curry : {A B C : Set} → (Pair A B → C) → (A → B → C)
sets-curry f = λ x y → f (mkPair x y)
\end{code}
%</cantor-curry>

%<*cantor-pair-prf>
\begin{code}
pairPrf' : {A B : Set} → {g : Pair A B}
         → mkPair (proj-pair true g) (proj-pair false g) ≡ g
pairPrf' {A} {B} {mkPair x x₁} = refl
\end{code}
%</cantor-pair-prf>

%<*cantor-curry'>
\begin{code}
set-curry′ : ∀ {A B C} (f : Pair A B → C) →
            ∃![ f' ∈ A ⇒ (B → C) ] ((x : Pair A B)
              → (set-eval ∘ (λ y → mkPair (f' (fst y)) (Function.id (snd y))))  x ≡ f x)
\end{code}
%</cantor-curry'>

\begin{code}
open ≡-Reasoning
\end{code}


%<*cantor-curry-uniq-type>
\begin{code}
sets-curry-unique : {A B C : Set} →
                    {f : Pair A B → C} →
                    {g : A → B → C} →
                    ((x : Pair A B) → g (proj-pair true x) (proj-pair false x) ≡ f x) →
                    (x : A) → (λ y → f (mkPair x y)) ≡ g x

\end{code}
%</cantor-curry-uniq-type>


%<*cantor-extensionality>
\begin{code}
Extensionality : (a b : Level) → Set _
Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
                     ----------------------------
                     (∀ x → f x ≡ g x) → f ≡ g
\end{code}
%</cantor-extensionality>

%<*cantor-postulate>
\begin{code}
postulate
  ext : Extensionality lzero lzero
\end{code}
%</cantor-postulate>

%<*cantor-curry-uniq>
\begin{code}
sets-curry-unique {f = f}{g = g} fprf x
  = let tproof = λ y → fprf (mkPair x y)
    in (begin
          (λ y → f (mkPair x y))
        ≡⟨ {!!} ⟩
          (λ y → g x y)
        ≡⟨ refl ⟩
          g x
        ∎  )
\end{code}
%</cantor-curry-uniq>

\begin{code}
sets-curry-unique' : {A B C : Set} →
  {f : Pair A B → C} →
  {g : A → B → C} →
  ((x : Pair A B) → g (proj-pair true x) (proj-pair false x) ≡ f x) →
  (x : A) → (λ y → f (mkPair x y)) ≡ g x
sets-curry-unique' {f = f}{g = g} fprf x
\end{code}

%<*cantor-curry-uniq1>
\begin{code}
  = let tproof = λ y → fprf (mkPair x y)
    in (begin
         (λ y → f (mkPair x y))
       ≡⟨ ext (λ t → sym (tproof t)) ⟩
         (λ y → g x y)
       ≡⟨ refl ⟩
         g x
       ∎  )
\end{code}
%</cantor-curry-uniq1>



%(y : .B) → g x y ≡ f (mkPair x y)

%<*cantor-sets-curry'-sat>
\begin{code}
sets-curry'-sat : ∀ {A B C} (f : Pair A B → C) → (x : Pair A B)
  → (set-eval ∘ (λ y → mkPair ((sets-curry f) (fst y)) (Function.id (snd y))))  x ≡ f x
\end{code}
%</cantor-sets-curry'-sat>

%<*cantor-sets-curry'-sat1>
\begin{code}
sets-curry'-sat = λ f x → begin
                            f (mkPair (proj-pair true x) (proj-pair false x))
                          ≡⟨ cong f pairPrf' ⟩
                            f x
                          ∎
\end{code}
%</cantor-sets-curry'-sat1>




%<*cantor-set-curry>
\begin{code}
set-curry′ f = Unique.Build.∃!-intro (sets-curry f) (λ x → sets-curry'-sat f x) sets-curry-unique
\end{code}
%</cantor-set-curry>

%<*cantor-exponential>
\begin{code}
set-exponential : {A B : Set} → Exp A B
set-exponential {A} {B} = record { Cᴮ = A → B ; eval = set-eval ; curry′  = set-curry′}
\end{code}
%</cantor-exponential>


%\begin{code}
%  curry′ = λ f →
%    Unique.Build.∃!-intro (sets-curry f)
%                          (λ x → cong f pairPrf' )
%                          λ x x₁ → {!!} }
%\end{code}


%<*cantor-hasexp>
\begin{code}
instance
  setsHasExponentials : HasExponentials Sets1
  setsHasExponentials = record { _↝′_ = λ B C → set-exponential }
\end{code}
%</cantor-hasexp>

\begin{code}
instance
  setsHasFiniteProducts : HasFiniteProducts Sets1
  setsHasFiniteProducts = record {}
\end{code}

\begin{code}
instance
  setsHasIsCCC : IsCCC Sets1
  setsHasIsCCC = record {}
\end{code}

\begin{code}
open HasExponentials setsHasExponentials
open Diagonal
\end{code}

%<*cantor-not>
\begin{code}
not : Bool → Bool
not false = true
not true = false
\end{code}
%</cantor-not>

%<*cantor-not-fx-type>
\begin{code}
not-fx-pt : ∀ {x} → (not x) ≢ x
\end{code}
%</cantor-not-fx-type>

%<*cantor-not-fx>
\begin{code}
not-fx-pt {false} ()
not-fx-pt {true} ()
\end{code}
%</cantor-not-fx>

\begin{code}
bool-no-fix-pt : {X : ⊤ → Bool} → not (X ⊤.tt) ≡ X ⊤.tt → ⊥
bool-no-fix-pt x = not-fx-pt x
\end{code}

%<*cantor-nofixpt>
\begin{code}
noFixPtBool : ¬ FixedPointProperty Bool
\end{code}
%</cantor-nofixpt>

%<*cantor-nofixpt1>
\begin{code}
noFixPtBool Y with (Y not)
\end{code}
%</cantor-nofixpt1>

%<*cantor-nof-def>
\begin{code}
... | record { X = X ; isFixedPoint = isFixedPoint } = {!!}
\end{code}
%</cantor-nof-def>


\begin{code}
noFixPtBool' : ¬ FixedPointProperty Bool
noFixPtBool' Y with (Y not)
\end{code}

%<*cantor-nof-final>
\begin{code}
... | record { X = X ; isFixedPoint = isFixedPoint } = not-fx-pt (isFixedPoint ⊤.tt)
\end{code}
%</cantor-nof-final>

\begin{code}
contradiction : ∀ {p w} {P : Set p} {Whatever : Set w} →
               P → ¬ P → Whatever
contradiction p ¬p = ⊥-elim (¬p p)
\end{code}

%<*cantor-cantor-type>
\begin{code}
cantorsDiagonalTheorem : ∀ {A} → ¬ PointSurjective A (A → Bool)
\end{code}
%</cantor-cantor-type>



%<*cantor-cantor>
\begin{code}
cantorsDiagonalTheorem = cantor Sets1 noFixPtBool
\end{code}
%</cantor-cantor>


\end{document}

