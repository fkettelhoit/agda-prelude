------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for reducer and reducel
------------------------------------------------------------------------

module Class.Reduce where

open import Data.List using (List; _∷_; [])
open import Level using (Level; suc)

------------------------------------------------------------------------
-- Type class

record reduceClass {a} (F : Set a → Set a) : Set (suc a) where
  field
    reducer : {A : Set a} {B : Set a} → (A → B → B) → F A → B → B
    reducel : {A : Set a} {B : Set a} → (B → A → B) → B → F A → B
  toList : {A : Set a} → F A → List A
  toList s = (reducer _∷_) s []

open reduceClass {{...}} public

------------------------------------------------------------------------
-- Instances

reduceInstanceList : {a : Level} → reduceClass List
reduceInstanceList {a} = record {
  reducer = λ {A} {B} f F x → Data.List.foldr {a} {a} {A} {B} f x F;
  reducel = Data.List.foldl }
