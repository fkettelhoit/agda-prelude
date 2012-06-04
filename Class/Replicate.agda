------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for replicate
------------------------------------------------------------------------

module Class.Replicate where

open import Data.List renaming (replicate to replicateList)
open import Data.Colist renaming (replicate to replicateColist)
open import Data.Vec using (Vec)

open import Level

------------------------------------------------------------------------
-- Type class

record replicateClass {a} {I : Set} (F : Set a → I → Set a) : Set (suc a) where
  field
    replicate : {A : Set a} → (n : I) → A → (F A n)

open replicateClass {{...}} public

------------------------------------------------------------------------
-- Instances

replicateInstanceList : {a : Level} → replicateClass (λ A n → List A)
replicateInstanceList {a} = record { replicate = replicateList {a = a} }

replicateInstanceColist : {a : Level} → replicateClass (λ A n → Colist A)
replicateInstanceColist {a} = record { replicate = replicateColist {a = a} }

replicateInstanceVec : {a : Level} → replicateClass Vec
replicateInstanceVec {a} =
  record { replicate = (λ n → Data.Vec.replicate {a = a}) }
