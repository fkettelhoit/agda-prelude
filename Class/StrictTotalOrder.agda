------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for strictTotalOrder
------------------------------------------------------------------------

module Class.StrictTotalOrder where

open import Data.Char renaming (strictTotalOrder to strictTotalOrderChar)
open import Data.String renaming (strictTotalOrder to strictTotalOrderString)

open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Type class

record strictTotalOrderClass {c ℓ₁ ℓ₂} (A : Set) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    strictTotalOrder : StrictTotalOrder c ℓ₁ ℓ₂

open strictTotalOrderClass {{...}} public

------------------------------------------------------------------------
-- Instances

strictTotalOrderInstanceChar : strictTotalOrderClass Char
strictTotalOrderInstanceChar =
  record { strictTotalOrder = strictTotalOrderChar }

strictTotalOrderInstanceString : strictTotalOrderClass String
strictTotalOrderInstanceString =
  record { strictTotalOrder = strictTotalOrderString }
