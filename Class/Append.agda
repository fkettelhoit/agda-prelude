------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for _++_
------------------------------------------------------------------------

module Class.Append where

open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Vec using (Vec)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤)
open import Level using (Level)

------------------------------------------------------------------------
-- Type class

record ++Class {f} (I : Set) (_+_ : I → I → I) (F : I → Set f)
       : Set (Level.suc f) where
  field
    _++_ : {n : I}{m : I} → F n → F m → F (n + m)
  infixr 5 _++_

open ++Class {{...}} public

------------------------------------------------------------------------
-- Instances

++InstanceColist : {a : Level} {A : Set a} → ++Class ⊤ _ (λ _  → Colist A)
++InstanceColist {a} = record { _++_ = Data.Colist._++_ {a = a} }

++InstanceList : {a : Level} {A : Set a} → ++Class ⊤ _ (λ _ → List A)
++InstanceList {a} = record { _++_ = Data.List._++_ {a = a} }

++InstanceString : ++Class ⊤ _ (λ _ → String)
++InstanceString = record { _++_ = Data.String._++_ }

++InstanceVec : {a : Level} {A : Set a} → ++Class ℕ _+_ (Vec A)
++InstanceVec {a} = record { _++_ = Data.Vec._++_ {a = a} }
