------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for setoid
------------------------------------------------------------------------

module Class.Setoid where

open import Data.Char renaming (setoid to setoidChar)
open import Data.Colist renaming (setoid to setoidColist)
open import Data.String renaming (setoid to setoidString)
open import Data.Unit renaming (setoid to setoidUnit)

open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Type class

record setoidClass {c ℓ a} (A : Set a) : Set (suc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ

open setoidClass {{...}} public

------------------------------------------------------------------------
-- Instances

setoidInstanceChar : setoidClass Char
setoidInstanceChar = record { setoid = setoidChar }

setoidInstanceColist : {c : Set} {a : Level} {A : Set a} →
                       setoidClass (Colist A)
setoidInstanceColist {c} = record { setoid = setoidColist c }

setoidInstanceString : setoidClass String
setoidInstanceString = record { setoid = setoidString }

setoidInstanceUnit : setoidClass Unit
setoidInstanceUnit = record { setoid = setoidUnit }
