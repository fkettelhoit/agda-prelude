------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for map
------------------------------------------------------------------------

module Class.Map where

open import Data.Colist renaming (map to mapColist)
open import Data.List renaming (map to mapList)
open import Data.Product renaming (map to mapProduct)
open import Data.Sum renaming (map to mapSum)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Unit using (⊤)

open import Level

------------------------------------------------------------------------
-- Type class

record mapClass {a f} (I : Set) (F : Set a → I → Set f) : Set (suc a ⊔ f) where
  field
    map : {A B : Set a} → {n : I} → (A → B) → F A n → F B n

open mapClass {{...}} public

------------------------------------------------------------------------
-- Instances

mapInstanceColist : {a : Level} → mapClass ⊤ (λ A _ → Colist A)
mapInstanceColist {a} = record { map = mapColist {b = a} }

mapInstanceList : {a : Level} → mapClass ⊤ (λ A _ → List A)
mapInstanceList {a} = record { map = mapList {b = a} }

mapInstanceVec : {a : Level} → mapClass ℕ Vec
mapInstanceVec {a} = record { map = Data.Vec.map {a = a} }
