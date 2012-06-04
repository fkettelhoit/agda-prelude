------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for fromList
------------------------------------------------------------------------

module Class.FromList where

open import Data.String using (String)
open import Data.Vec using (Vec)
open import Data.Colist using (Colist)

open import Data.Nat using (ℕ)
open import Data.Char using (Char)
open import Data.List using (List; length)
open import Level

------------------------------------------------------------------------
-- Type class

record fromListClass {a : Level} {b : Level} (A : Set a) (B : ℕ → Set b)
                     : Set (suc (b ⊔ a)) where
  field
    fromList : (l : List A) → B (length l)

open fromListClass {{...}} public

------------------------------------------------------------------------
-- Instances

fromListInstanceColist : {a : Level} → {A : Set a} → fromListClass A
                         (λ n → Colist A)
fromListInstanceColist {a} {A} =
  record { fromList = Data.Colist.fromList {a = a} {A = A} }

fromListInstanceString : fromListClass Char (λ n → String)
fromListInstanceString = record { fromList = Data.String.fromList }

fromListInstanceVec : {a : Level} → {A : Set a} → fromListClass A (Vec A)
fromListInstanceVec {a} {A} =
  record { fromList = Data.Vec.fromList {a = a} {A = A} }
