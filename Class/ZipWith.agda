------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for zipWith and zip
------------------------------------------------------------------------

module Class.ZipWith where

open import Coinduction
open import Data.Colist using (Colist; []; _∷_)
open import Data.List using (List)
open import Data.Stream using (Stream)
open import Data.Vec using (Vec)

open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

open import Level

------------------------------------------------------------------------
-- Type class

record zipWithClass {a} {b} {c} (I : Set) (F : Set a → I → Set a)
                                          (G : Set b → I → Set b)
                                          (H : Set c → I → Set c)
                    : Set (suc a ⊔ suc b ⊔ suc c) where
  field
    zipWith : {A : Set a} {B : Set b} {C : Set c} {n : I} →
              (A → B → C) → F A n → G B n → H C n

open zipWithClass {{...}} public

zip : ∀ {a b} {I : Set}
  {F : Set a → I → Set a}
  {G : Set b → I → Set b}
  {H : Set (a ⊔ b) → I → Set (a ⊔ b)}
  {{ z : zipWithClass I F G H }}
  {A : Set a} {B : Set b} {n : I} → F A n → G B n → H (A × B) n
zip = zipWith _,_

------------------------------------------------------------------------
-- Instances

zipWithColist : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              → (A → B → C) → Colist A → Colist B → Colist C
zipWithColist f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ (zipWithColist f (♭ xs) (♭ ys))
zipWithColist f _        _        = []

zipWithInstanceColist  : ∀ {a b c} → zipWithClass ⊤ (λ A n → Colist A)
                         (λ A n → Colist A) (λ A n → Colist A)
zipWithInstanceColist {a} {b} {c} =
  record { zipWith = zipWithColist {a} {b} {c} }

zipWithInstanceList : ∀ {a b c} → zipWithClass ⊤ (λ A n → List A)
                      (λ A n → List A) (λ A n → List A)
zipWithInstanceList {a} {b} {c} =
  record { zipWith = Data.List.zipWith {a} {b} {c} }

zipWithInstanceStream : zipWithClass ⊤ (λ A n → Stream A) (λ A n → Stream A)
                        (λ A n → Stream A)
zipWithInstanceStream = record { zipWith = Data.Stream.zipWith }

zipWithInstanceVec : ∀ {a b c} → zipWithClass ℕ Vec Vec Vec
zipWithInstanceVec {a} {b} {c} =
  record { zipWith = Data.Vec.zipWith {a} {b} {c} }


