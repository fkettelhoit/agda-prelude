------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for reverse
------------------------------------------------------------------------

module Class.Reverse where

open import Data.List using (List)
open import Data.Vec using (Vec)

open import Data.Nat
open import Data.Unit
open import Level using (Level)

------------------------------------------------------------------------
-- Type class

record reverseClass {a : Level} (I : Set) (F : Set a → I → Set a)
                    : Set (Level.suc a) where
  field
    reverse : {A : Set a} → {n : I} → F A n → F A n

open reverseClass {{...}} public

------------------------------------------------------------------------
-- Instances

reverseInstanceList : {a : Level} → reverseClass ⊤ (λ A _ → List A)
reverseInstanceList {a} = record { reverse = Data.List.reverse {a = a} }

reverseInstanceVec : {a : Level} → reverseClass ℕ Vec
reverseInstanceVec {a} = record { reverse = Data.Vec.reverse {a = a} }
