------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for _∈_ and _∉_
------------------------------------------------------------------------

module Class.Member where

open import Data.List using (List)
open import Data.List.Any using (module Membership-≡)
open Membership-≡ hiding (_∉_) renaming (_∈_ to _∈List_)
open import Data.Colist using (Colist)
open import Data.Vec using (Vec)

open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Level using (Level; suc)

------------------------------------------------------------------------
-- Type class

record ∈Class {a} (I : Set) (F : Set a → I → Set a) : Set (suc a) where
  field
    _∈_ : {A : Set a} → A → {n : I} → (F A n) → Set a
  infixr 5 _∈_
  _∉_ : {A : Set a} → A → {n : I} → (F A n) → Set a
  _∉_ x xs = ¬ (x ∈ xs)
  infixr 5 _∉_

open ∈Class {{...}} public

------------------------------------------------------------------------
-- Instances

∈InstanceColist : {a : Level} → ∈Class ⊤ (λ A n → Colist A)
∈InstanceColist {a} = record { _∈_ = λ {A} x {n} F →
                                     Data.Colist._∈_ {a = a} {A} x F }

∈InstanceList : {a : Level} → ∈Class ⊤ (λ A n → List A)
∈InstanceList {a} = record { _∈_ = λ {A} x {n} F → _∈List_ {a = a} {A} x F }

∈InstanceVec : {a : Level} → ∈Class ℕ Vec
∈InstanceVec {a} = record { _∈_ = Data.Vec._∈_ {a = a} }
