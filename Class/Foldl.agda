------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for foldl
------------------------------------------------------------------------

module Class.Foldl where

open import Data.List using (List)
open import Data.Vec using (Vec)

open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- Type class

record foldlClass {a b} (N : Set)(zero : N)(suc : N → N)
    (F : Set a → N → Set a) : Set (Level.suc (a ⊔ b))
  where
  field
    foldl : {A : Set a}{B : N → Set b}
      (f : {n : N} → B n → A → B (suc n))
      (b : B zero) →
      {n : N} → F A n → B n

open foldlClass {{...}} public

------------------------------------------------------------------------
-- Instances

foldlInstanceList : {a b : Level} → foldlClass ⊤ _ _ (λ A n → List A)
foldlInstanceList {a} {b} = record { foldl = λ {A} {B} f x {n} →
  Data.List.foldl {a} {b} {B _} {A} f x }

foldlInstanceVec : {a b : Level} → foldlClass ℕ zero suc Vec
foldlInstanceVec {a} {b} = record { foldl = λ {A} {B} f x {n} →
  Data.Vec.foldl {a} {b} {A} B {n} f x }
