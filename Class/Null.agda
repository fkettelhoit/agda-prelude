------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for null
------------------------------------------------------------------------

module Class.Null where

open import Data.List using (List)
open import Data.Colist using (Colist)

open import Data.Bool using (Bool)
open import Level using (Level; suc)

------------------------------------------------------------------------
-- Type class

record nullClass {a} (F : Set a → Set a) : Set (suc a) where
  field
    null : {A : Set a} → (F A) → Bool

open nullClass {{...}} public

------------------------------------------------------------------------
-- Instances

nullInstanceList : {a : Level} → nullClass List
nullInstanceList {a} = record { null = Data.List.null {a} }

nullInstanceColist : {a : Level} → nullClass Colist
nullInstanceColist {a} = record { null = Data.Colist.null {a} }

