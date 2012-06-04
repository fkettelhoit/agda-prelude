------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for decTotalOrder
------------------------------------------------------------------------

module Class.DecTotalOrder where

import Data.Nat as Nat; open import Data.Nat using (ℕ)
open import Data.Unit renaming (decTotalOrder to decTotalOrder⊤)

open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Type class

record decTotalOrderClass {c ℓ₁ ℓ₂} (A : Set) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    decTotalOrder : DecTotalOrder c ℓ₁ ℓ₂

open decTotalOrderClass {{...}} public

------------------------------------------------------------------------
-- Instances

decTotalOrderInstanceℕ : decTotalOrderClass ℕ
decTotalOrderInstanceℕ = record { decTotalOrder = Nat.decTotalOrder }

decTotalOrderInstance⊤ : decTotalOrderClass ⊤
decTotalOrderInstance⊤ = record { decTotalOrder = decTotalOrder⊤ }
