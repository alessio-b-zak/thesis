module Combinatory where

open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Setoid)
open import Relation.Binary.EqReasoning as EqReasoning


module Applicative where
  record ApplicativeStruct lo l≈ : Set (suc (lo ⊔ l≈)) where
    infixl 9 _∙_

    field
      Obj : Set lo
      _∙_ : Obj → Obj → Obj


  IsExtensional : ∀ {lo l≈} → ApplicativeStruct lo l≈ → Set lo
  IsExtensional A = {x y z : Obj} → ((x ∙ z ≡ y ∙ z) → x ≡ y)
    where open ApplicativeStruct A



module CombAlg where

  open Applicative

  record CombinatoryAlgebra lo l≈ : Set (suc (lo ⊔ l≈)) where
    field
      App : ApplicativeStruct lo l≈

    open ApplicativeStruct App public

    field
      K : Obj
      S : Obj
      K-axiom : {x y : Obj} → K ∙ x ∙ y ≡ x
      S-axiom : {x y z : Obj} → S ∙ x ∙ y ∙ z ≡ x ∙ z ∙ (y ∙ z)

    I : Obj
    I = S ∙ K ∙ K

    ε : Obj
    ε = S ∙ (K ∙ I)

    T : Obj
    T = K

    F : Obj
    F = K ∙ I

  IsWeaklyExtensional : ∀ {lo l≈} →  CombinatoryAlgebra lo l≈ → Set lo
  IsWeaklyExtensional c = {x y z : Obj} → ((x ∙ z ≡ y ∙ z) → (ε ∙ x ≡ ε ∙ y))
    where open CombinatoryAlgebra c


module LamAlgebra where

  open CombAlg
  open Applicative

  record LambdaAlgebra lo l≈ : Set (suc (lo ⊔ l≈)) where
    field
      combAlg : CombinatoryAlgebra lo l≈

    open CombinatoryAlgebra combAlg public

    field
      CurryAxiom1 : K ≡ S ∙ (S ∙ (K ∙ S)) ∙ (S ∙ (K ∙ K) ∙ K) ∙ (K ∙ (S ∙ K ∙ K))

      CurryAxiom2 : S ≡ S ∙ (S ∙ ( K ∙ S)) ∙ (S ∙ (K ∙ ( S ∙ (K ∙ S))) ∙
                            (S ∙ (K ∙ (S ∙ (K ∙ K))) ∙ S) ∙ (K ∙ (K ∙ (S ∙ K ∙ K))))

      CurryAxiom3 : S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ (S ∙ (K ∙ S) ∙ K))) ∙ (K ∙ K)
                      ≡ S ∙ (K ∙ K)

      CurryAxiom4 : S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K)) ≡
                      S ∙ (K ∙ K) ∙ (S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙ (S ∙ K ∙ K)))
                        ∙ (K ∙ (S ∙ K ∙ K)))

      CurryAxiom5 : S ∙ (K ∙ (S ∙ (K ∙ S))) ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ S)))
                    ≡ S ∙ (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ K) ∙
                      (S ∙ (K ∙ S) ∙ (S ∙ (K ∙ (S ∙ (K ∙ S))) ∙ S)))) ∙ (K ∙ S)



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
 
