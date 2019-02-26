module categories where

open import Relation.Binary
open import Level

record Category (a : Level) (Obj : Set a) : Set (suc a) where
  field
    -- Levels are probably messed up
    _↣_ : Rel Obj a
    _∘_  : {A B C : Obj} → (A ↣ B) → (B ↣ C) → (A ↣ C)
     
