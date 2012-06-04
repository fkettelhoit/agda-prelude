------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for concat
------------------------------------------------------------------------

module Class.Concat where

open import Data.List using (List)
open import Data.Colist using (Colist)
open import Data.Vec using (Vec)

open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ; _*_)
open import Data.Unit
open import Level

------------------------------------------------------------------------
-- Type class

record concatClass {a} (I : Set) (_+_ : I → I → I) (F : Set a → I → Set a)
                       (G : Set a → I → Set a) : Set (suc a) where
  field
    concat : {A : Set a}{m : I}{n : I} → F (G A m) n → F A (n + m)

open concatClass {{...}} public

------------------------------------------------------------------------
-- Instances

concatInstanceColist : {a : Level} → concatClass ⊤ (λ _ _ → _)
                       (λ A _ → Colist A) (λ A _ → List⁺ A)
concatInstanceColist {a} = record { concat = Data.Colist.concat {a = a} }

concatInstanceList : {a : Level} → concatClass ⊤ (λ _ _ → _)
                     (λ A _ → List A) (λ A _ → List A)
concatInstanceList {a} = record { concat = Data.List.concat {a = a} }

concatInstanceVec : {a : Level} → concatClass ℕ _*_ Vec Vec
concatInstanceVec {a} = record { concat = Data.Vec.concat {a = a} }
