module Combinatory where


open import Level
import Retract
open import Data.Product
import Relation.Binary.EqReasoning as EqReasoning
open import Data.String
open import Cats.Category.Base
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Setoid)
--open import Relation.Binary.EqReasoning as EqReasoning


module Applicative where
  record ApplicativeStruct lo l≈ : Set (suc (lo ⊔ l≈)) where
    infixl 9 _∙_

    field
      {{Underlying}} : Setoid lo l≈

    open Setoid Underlying public renaming (Carrier to Obj)
    open EqReasoning Underlying public
    module ≈ = IsEquivalence ((Setoid.isEquivalence Underlying))

    field
      _∙_ : Obj → Obj → Obj
      ∙-resp : _∙_  Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

    ∙-resp-l : {A : Obj} → (_∙_ A) Preserves _≈_ ⟶ _≈_
    ∙-resp-l eq = ∙-resp ≈.refl eq

    ∙-resp-r : {b : Obj} → (λ a → _∙_ a b) Preserves _≈_ ⟶ _≈_
    ∙-resp-r eq = ∙-resp eq ≈.refl


  IsExtensional : ∀ {lo l≈} → ApplicativeStruct lo l≈ → Set (lo ⊔ l≈)
  IsExtensional A = {x y z : Obj} → ((x ∙ z ≈ y ∙ z) → x ≈ y)
    where open ApplicativeStruct A



module CombAlg where

  open Applicative

  record CombinatoryAlgebra lo l≈ : Set (suc (lo ⊔ l≈)) where
    field
      {{App}} : ApplicativeStruct lo l≈

    open ApplicativeStruct App public

    field
      K : Obj
      S : Obj
      K-axiom : {x y : Obj} → K ∙ x ∙ y ≈ x
      S-axiom : {x y z : Obj} → S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)

    I : Obj
    I = S ∙ K ∙ K

    ε : Obj
    ε = S ∙ (K ∙ I)

    T : Obj
    T = K

    F : Obj
    F = K ∙ I

    Id-I : {A : Obj} → I ∙ A ≈ A
    Id-I {A} = begin
                 I ∙ A
               ≈⟨ ≈.refl ⟩
                 S ∙ K ∙ K ∙ A
               ≈⟨ S-axiom ⟩
                 K ∙ A ∙ (K ∙ A)
               ≈⟨ K-axiom ⟩
                 A
               ∎

  IsWeaklyExtensional : ∀ {lo l≈} →  CombinatoryAlgebra lo l≈ → (Set (lo ⊔ l≈))
  IsWeaklyExtensional c = {x y z : Obj} → ((x ∙ z ≈ y ∙ z) → (ε ∙ x ≈ ε ∙ y))
    where open CombinatoryAlgebra c


module LamAlgebra where

  open CombAlg
  open Applicative

  record LambdaAlgebra lo l≈ : Set (suc (lo ⊔ l≈)) where
    field
     {{combAlg}} : CombinatoryAlgebra lo l≈

    open CombinatoryAlgebra combAlg public

    field
      CurryAxiom1 : K ≈ S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K)) ∙ (K ∙ I)

      CurryAxiom2 : S ≈ S ∙ (S ∙ ( K ∙ S) ∙ (S ∙ (K ∙ ( S ∙ (K ∙ S))) ∙
                            (S ∙ (K ∙ (S ∙ (K ∙ K))) ∙ S))) ∙ (K ∙ (K ∙ I))

      CurryAxiom3 : S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ (S ∙ (K ∙ S) ∙ K))) ∙ (K ∙ K)
                      ≈ S ∙ (K ∙ K)

      CurryAxiom4 : S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K)) ≈
                      S ∙ (K ∙ K) ∙ (S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ I))
                        ∙ (K ∙ I))

      CurryAxiom5 : S ∙ (K ∙ (S ∙ (K ∙ S))) ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ S)))
                    ≈ S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙
                      (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ (S ∙ (K ∙ S))) ∙ S)))) ∙ (K ∙ S)

      Decurry : {A B : Obj} → K ∙ (A ∙ B) ≈ S ∙ (K ∙ A) ∙ (K ∙ B)

    infixr 9 _●_

    _●_ : Obj → Obj → Obj
    _●_ A B = S ∙ (K ∙ S) ∙ K ∙ A ∙ B

    ●-is-comp : ∀ {A B C} → (A ● B) ∙ C ≈ (A ∙ (B ∙ C))
    ●-is-comp {A} {B} {C} =
                 begin
                   (A ● B) ∙ C
                 ≈⟨ ≈.refl ⟩
                   S ∙ (K ∙ S) ∙ K ∙ A ∙ B ∙ C
                 ≈⟨ ∙-resp-r (∙-resp-r S-axiom) ⟩
                   K ∙ S ∙ A ∙ (K ∙ A) ∙ B ∙ C
                 ≈⟨ ∙-resp-r (∙-resp-r (∙-resp-r K-axiom)) ⟩
                   S ∙ (K ∙ A) ∙ B ∙ C
                 ≈⟨ S-axiom ⟩
                   K ∙ A ∙ C ∙ (B ∙ C)
                 ≈⟨ ∙-resp-r K-axiom ⟩
                   (A ∙ (B ∙ C))
                 ∎



-- K ∙ A ≈ S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K)) ∙ (K ∙ I) ∙ A
-- K ∙ A ≈ S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K) ∙ A ∙ ((K ∙ I) ∙ A)
-- K ∙ A ≈ S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K) ∙ A ∙ ((K ∙ I) ∙ A)
-- K ∙ A ≈ (K ∙ S ∙ A) ∙ ((S ∙ (K ∙ K) ∙ K) ∙ A) ∙ (K ∙ I ∙ A)
-- K ∙ A ≈  S ∙ ((S ∙ (K ∙ K) ∙ K) ∙ A) ∙ (K ∙ I ∙ A)
-- K ∙ A ≈  S ∙ (S ∙ (K ∙ K) ∙ K ∙ A) ∙ I
-- K ∙ A ≈  S ∙ (K ∙ K ∙ A ∙ (K ∙ A)) ∙ I
-- K ∙ A ≈  S ∙ (K ∙ K ∙ A) ∙ I
-- K ∙ A ≈  S ∙ K ∙ I
-- K ∙ A ≈  S ∙ K ∙ (S ∙ K ∙ K)

    C-axiom1-App : {A : Obj} → K ∙ A ≈ S ∙ (K ∙ (K ∙ A)) ∙ I
    C-axiom1-App {A} = begin
                         K ∙ A
                       ≈⟨ ∙-resp-r CurryAxiom1 ⟩
                         S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K)) ∙ (K ∙ I) ∙ A
                       ≈⟨ S-axiom ⟩
                         S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ K) ∙ A ∙ ((K ∙ I) ∙ A)
                       ≈⟨ ∙-resp-r S-axiom ⟩
                         (K ∙ S ∙ A) ∙ ((S ∙ (K ∙ K) ∙ K) ∙ A) ∙ (K ∙ I ∙ A)
                       ≈⟨ ∙-resp-r (∙-resp-r K-axiom) ⟩
                         S ∙ ((S ∙ (K ∙ K) ∙ K) ∙ A) ∙ (K ∙ I ∙ A)
                       ≈⟨ ∙-resp-l K-axiom ⟩
                         S ∙ (S ∙ (K ∙ K) ∙ K ∙ A) ∙ I
                       ≈⟨ ∙-resp-r (∙-resp-l S-axiom) ⟩
                         S ∙ (K ∙ K ∙ A ∙ (K ∙ A)) ∙ I
                       ≈⟨ ∙-resp-r (∙-resp-l (∙-resp-r K-axiom)) ⟩
                         S ∙ (K ∙ (K ∙ A)) ∙ I
                       ∎

-- A ● B = λ x . a (b x)
-- (A ● B) ● C = A ● (B ● C)
-- λ z . ((λ x . a (b x)) z) (c z)
-- λ z . (a(b(c z)))
-------------
-- λ z . a ((λ x . b (c x)) z)
-- λ z . a(b(cz))


    ●-assoc : {A B C : Obj} → (A ● B) ● C ≈ A ● (B ● C)
    ●-assoc {A} {B} {C} = begin
                             (A ● B) ● C
                           ≈⟨ ≈.refl ⟩
                             S ∙ (K ∙ S) ∙ K ∙ (S ∙ (K ∙ S) ∙ K ∙ A ∙ B) ∙ C
                           ≈⟨ ∙-resp-r (∙-resp-l (∙-resp-r S-axiom)) ⟩
                             S ∙ (K ∙ S) ∙ K ∙ (K ∙ S ∙ A ∙ (K ∙ A) ∙ B) ∙ C
                           ≈⟨ ∙-resp-r (∙-resp-l (∙-resp-r (∙-resp-r K-axiom))) ⟩
                             S ∙ (K ∙ S)  ∙ K ∙ (S ∙ (K ∙ A) ∙ B) ∙ C
                           ≈⟨ ∙-resp-r S-axiom ⟩
                             K ∙ S ∙ (S ∙ (K ∙ A) ∙ B) ∙ (K ∙ (S ∙ (K ∙ A) ∙ B)) ∙ C
                           ≈⟨ ∙-resp-r (∙-resp-r K-axiom) ⟩
                             S ∙ (K ∙ (S ∙ (K ∙ A) ∙ B)) ∙ C
                           ≈⟨ {!!} ⟩
                             S ∙ (K ∙ A) ∙ (S ∙ (K ∙ B) ∙ C)
                           ≈⟨ ≈.sym (∙-resp-r (∙-resp-r K-axiom)) ⟩
                             K ∙ S ∙ A ∙ (K ∙ A) ∙ (S ∙ (K ∙ B) ∙ C)
                           ≈⟨ ≈.sym (∙-resp-r S-axiom) ⟩
                             S ∙ (K ∙ S) ∙ K ∙ A ∙ (S ∙ (K ∙ B) ∙ C)
                           ≈⟨ ≈.sym (∙-resp-l (∙-resp-r (∙-resp-r K-axiom))) ⟩
                             S ∙ (K ∙ S) ∙ K ∙ A ∙ ( K ∙ S ∙ B ∙ (K ∙ B) ∙ C)
                           ≈⟨ ≈.sym (∙-resp-l (∙-resp-r S-axiom)) ⟩
                             S ∙ (K ∙ S) ∙ K ∙ A ∙ (S ∙ (K ∙ S) ∙ K ∙ B ∙ C)
                           ≈⟨ ≈.refl ⟩
                             A ● (B ● C)
                           ∎

    Obj-idem-● : Obj → Set l≈
    Obj-idem-● A = A ● A ≈ A

    commutator-arrow : Obj → Obj → Obj → Set l≈
    commutator-arrow a b f = b ● f ● a ≈ f

module LambdaModel where
  open CombAlg
  open Applicative
  open LamAlgebra

  record LambdaModel lo l≈ : Set (suc (lo ⊔ l≈)) where
    field
      lambdaAlgebra : LambdaAlgebra lo l≈

    open LambdaAlgebra lambdaAlgebra public

    field
      isWeaklyExtensional : IsWeaklyExtensional combAlg

-- todo: term model as a lambda model. lamda model to ccc. term model to ccc. diagonal


module Monom where
  open CombAlg
  open Applicative
  open LamAlgebra
  open Setoid
  open ApplicativeStruct

  infixl 8 _#_


  data Monomial {lo l≈} (A : ApplicativeStruct lo l≈) : Set (lo ⊔ l≈) where
    Term : String → Monomial A
    Const : (Carrier (Underlying A)) → Monomial A
    _#_ :  Monomial A → Monomial A → Monomial A



  Valuation : {lo l≈ : Level} (A : ApplicativeStruct lo l≈) → Set lo
  Valuation {lo} {l≈} A = String → (Carrier (Underlying A))


  intepret : {lo l≈ : Level} {A : ApplicativeStruct lo l≈}
           → Valuation A
           → Monomial A
           → (Carrier (Underlying A))
  intepret val (Term x₁) = val x₁
  intepret val (Const x₁) = x₁
  intepret {lo} {l≈} {A} val (y # y₁) = _∙_ A (intepret val y) (intepret val y₁)


module KaroubiEnvelope where
  open CombAlg
  open Applicative
  open LamAlgebra
  open Setoid
  open Retract
  open Data.Product
  open Σ
--  open LambdaAlgebra {{...}}
--  open ApplicativeStruct {{...}}
--  open CombinatoryAlgebra {{...}}


  karoubi : {lo l≈ a b c : Level}
          → LambdaAlgebra a b
          → Σ (Category (a ⊔ b) (a ⊔ b) (a ⊔ b)) HasRetraction
  karoubi {lo} {l≈} x = (record
                { Obj = Σ Obj Obj-idem-●
                 ; _⇒_ = λ x₁ x₂ → Σ Obj ((commutator-arrow (proj₁ x₁) (proj₁ x₂)))
                 ; _≈_ = {!!}
                 ; id = {!!}
                 ; _∘_ = {!!}
                 ; equiv = {!!}
                 ; ∘-resp = {!!}
                 ; id-r = {!!}
                 ; id-l = {!!}
                 ; assoc = {!!}
                 }) , (record { reflexive = {!!} ; isReflexive = {!!} })
          where open LambdaAlgebra x
          -- rejig the above line to qualify it
          -- think about equivalence relation
          -- Prove cong of Obj-idem-●
          -- work out what combinators look like in this category
--karoubi envelope, has retraction,
