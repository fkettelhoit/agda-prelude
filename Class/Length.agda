------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for length
------------------------------------------------------------------------

module Class.Length where

open import Data.List using (List)
open import Data.Colist using (Colist)

open import Level using (Level; suc)

------------------------------------------------------------------------
-- Type class

record lengthClass {a} {n : Set} (F : Set a → Set a) : Set (suc a) where
  field
    length : {A : Set a} → (F A) → n

open lengthClass {{...}} public

------------------------------------------------------------------------
-- Instances

lengthInstanceList : {a : Level} → lengthClass List
lengthInstanceList {a} = record { length = Data.List.length {a} }

lengthInstanceColist : {a : Level} → lengthClass Colist
lengthInstanceColist {a} = record { length = Data.Colist.length {a} }

