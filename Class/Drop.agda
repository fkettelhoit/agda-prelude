------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for drop
------------------------------------------------------------------------

module Class.Drop where

open import Coinduction
open import Data.Colist using (Colist; []; _∷_)
open import Data.List using (List)
open import Data.Stream using (Stream)
open import Data.Vec using (Vec)

open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_)

open import Level using (Level; suc)

------------------------------------------------------------------------
-- Type class

record dropClass {a} (I : Set) (_+_ : ℕ → I → I)
                     (F : Set a → I → Set a) : Set (suc a) where
  field
    drop : {A : Set a} → (m : ℕ) → {n : I} → F A (m + n)→ F A n

open dropClass {{...}} public

------------------------------------------------------------------------
-- Instances

dropColist : ∀ {a} {A : Set a} → ℕ → Colist A → Colist A
dropColist Data.Nat.zero    xs       = xs
dropColist (Data.Nat.suc n) []       = []
dropColist (Data.Nat.suc n) (x ∷ xs) = dropColist n (♭ xs)

dropInstanceColist : {a : Level} → dropClass ⊤ _ (λ A n → Colist A)
dropInstanceColist {a} = record { drop = λ m → dropColist {a} m }

dropInstanceList : {a : Level} → dropClass ⊤ _ (λ A n → List A)
dropInstanceList {a} = record { drop = λ m → Data.List.drop {a} m }

dropInstanceStream : dropClass ⊤ _ (λ A n → Stream A)
dropInstanceStream = record { drop = λ m → Data.Stream.drop m }

dropInstanceVec : {a : Level} → dropClass ℕ _+_ Vec
dropInstanceVec {a} = record { drop = Data.Vec.drop {a} }
