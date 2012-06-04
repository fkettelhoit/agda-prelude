------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for foldr
------------------------------------------------------------------------

module Class.Foldr where

open import Data.List using (List)
open import Data.Vec using (Vec)

open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- Type class

record foldrClass {a b} (N : Set)(zero : N)(suc : N → N)
    (F : Set a → N → Set a) : Set (Level.suc (a ⊔ b))
  where
  field
    foldr : {A : Set a}{B : N → Set b}
      (f : {n : N} → A → B n → B (suc n))
      (b : B zero) →
      {n : N} → F A n → B n

open foldrClass {{...}} public

------------------------------------------------------------------------
-- Instances

foldrInstanceList : {a b : Level} → foldrClass ⊤ _ _ (λ A n → List A)
foldrInstanceList {a} {b} = record { foldr = λ {A} {B} f x {n} →
  Data.List.foldr {a} {b} {A} {B _} f x }

foldrInstanceVec : {a b : Level} → foldrClass ℕ zero suc Vec
foldrInstanceVec {a} {b} = record { foldr = λ {A} {B} f x {n} →
  Data.Vec.foldr {a} {b} {A} B {n} f x }
