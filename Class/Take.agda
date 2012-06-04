------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for take
------------------------------------------------------------------------

module Class.Take where

open import Data.Nat
open import Data.BoundedVec.Inefficient as BVec
  using (BoundedVec; []; _∷_)
open import Data.List renaming (take to takeListOrig)
open import Data.Colist renaming (take to takeColist)
open import Data.Vec using (Vec)

open import Data.Unit using (⊤)

open import Level renaming (zero to lzero; suc to lsuc)

------------------------------------------------------------------------
-- Type class

record takeClass {a} (I : Set) (FI : ℕ → I → I)
                 (F : Set a → I → Set a)
                 (G : Set a → ℕ → Set a) : Set (lsuc a) where
  field
    take : {A : Set a} → (m : ℕ) → {n : I} → F A (FI m n)→ G A m

open takeClass {{...}} public

------------------------------------------------------------------------
-- Instances

takeList : ∀ {a} {A : Set a} → (n : ℕ) → List A → BoundedVec A n
takeList zero    xs       = []
takeList (suc n) []       = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

takeInstanceList : {a : Level} → takeClass ⊤ (λ _ _ → _) (λ A n → List A)
                   BoundedVec
takeInstanceList {a} = record { take = λ m → takeList {a = a} m }

takeInstanceListOrig : {a : Level} → takeClass ⊤ (λ _ _ → _) (λ A n → List A)
                       (λ A n → List A) 
takeInstanceListOrig {a} = record { take = λ m → takeListOrig {a = a} m }

takeInstanceColist : {a : Level} → takeClass ⊤ (λ _ _ → _) (λ A n → Colist A)
                     BoundedVec
takeInstanceColist {a} = record { take = λ m → takeColist {a = a} m }

takeInstanceVec : {a : Level} → takeClass ℕ _+_ Vec Vec
takeInstanceVec {a} = record { take = Data.Vec.take {a = a} }
