------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for decSetoid
------------------------------------------------------------------------

module Class.DecSetoid where

open import Data.Bool renaming (decSetoid to decSetoidBool)
open import Data.Char renaming (decSetoid to decSetoidChar)
open import Data.String renaming (decSetoid to decSetoidString)
open import Data.Unit renaming (decSetoid to decSetoidUnit)

open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Type class

record decSetoidClass {c ℓ} (A : Set) : Set (suc (c ⊔ ℓ)) where
  field
    decSetoid : DecSetoid c ℓ

open decSetoidClass {{...}} public

------------------------------------------------------------------------
-- Instances

decSetoidInstanceBool : decSetoidClass Bool
decSetoidInstanceBool = record { decSetoid = decSetoidBool }

decSetoidInstanceChar : decSetoidClass Char
decSetoidInstanceChar = record { decSetoid = decSetoidChar }

decSetoidInstanceString : decSetoidClass String
decSetoidInstanceString = record { decSetoid = decSetoidString }

decSetoidInstanceUnit : decSetoidClass Unit
decSetoidInstanceUnit = record { decSetoid = decSetoidUnit }
