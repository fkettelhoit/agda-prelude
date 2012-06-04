------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for _≟_
------------------------------------------------------------------------

module Class.DecEq where

open import Data.Bool using (Bool)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Unit using (⊤)

open import Relation.Binary.Core

------------------------------------------------------------------------
-- Type class

record ≟Class (A : Set) : Set where
  field
    _≟_ : Decidable {A = A} _≡_

open ≟Class {{...}} public

------------------------------------------------------------------------
-- Instances

≟InstanceBool : ≟Class Bool
≟InstanceBool = record { _≟_ = Data.Bool._≟_ }

≟InstanceChar : ≟Class Char
≟InstanceChar = record { _≟_ = Data.Char._≟_ }

≟Instanceℕ : ≟Class ℕ
≟Instanceℕ = record { _≟_ = Data.Nat._≟_ }

≟InstanceString : ≟Class String
≟InstanceString = record { _≟_ = Data.String._≟_ }

≟Instance⊤ : ≟Class ⊤
≟Instance⊤ = record { _≟_ = Data.Unit._≟_ }
