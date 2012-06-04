------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for [_]
------------------------------------------------------------------------

module Class.ListLiteral where

open import Data.List renaming ([_] to [_]List)
open import Data.Colist renaming ([_] to [_]Colist)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

open import Level

------------------------------------------------------------------------
-- Type class

record [_]Class {a} (F : Set a → ℕ → Set a) : Set (suc a) where
  field
    [_] : {A : Set a} → A → (F A 1)

open [_]Class {{...}} public

------------------------------------------------------------------------
-- Instances

[_]InstanceList : {a : Level} → [_]Class (λ A _ → List A)
[_]InstanceList {a} = record { [_] = [_]List {a = a} }

[_]InstanceColist : {a : Level} → [_]Class (λ A _ → Colist A)
[_]InstanceColist {a} = record { [_] = [_]Colist {a = a} }

[_]InstanceVec : {a : Level} → [_]Class Vec
[_]InstanceVec {a} = record { [_] = Data.Vec.[_] {a = a} }

