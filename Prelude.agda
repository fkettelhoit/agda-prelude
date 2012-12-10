------------------------------------------------------------------------
-- The Agda standard library
--
-- A bundle of several often used modules, with name clashes between
-- modules resolved using type classes
------------------------------------------------------------------------

module Prelude where

------------------------------------------------------------------------
-- Basics

open import Function public
  using (_$_; _∘_; _∘′_; id; const; flip; _∋_)
open import Level public using (Level)
open import Size public using (Size; ↑_)

------------------------------------------------------------------------
-- IO

open import Coinduction public hiding (unfold)
open import IO public
  using (IO; run; sequence; sequence′; mapM; mapM′; getContents; readFile;
        readFiniteFile; writeFile∞; writeFile; appendFile∞; appendFile;
        putStr∞; putStr; putStrLn∞; putStrLn)
  renaming (_>>=_ to _∞>>=_; return to ∞return)

------------------------------------------------------------------------
-- IO (experimental)

open import IO.Environment public

------------------------------------------------------------------------
-- Data types

open import Data.Bool public
  using (Bool; true; false; not; if_then_else_; _∧_; _∨_; T; _xor_)
open import Data.Char public using (Char; toNat)
open import Data.Colist public using (Colist; []; _∷_; lookup)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Fin public using (Fin; zero; suc; toℕ)
open import Data.List public
  using (List; []; _∷_; intersperse; takeWhile; dropWhile)
open import Data.List.Any public
  using (module Membership-≡; there; here)
open import Data.Maybe public using (Maybe; just; nothing; maybe; maybe′)
open import Data.Nat public using (ℕ; zero; suc; _+_; _∸_; _*_; _⊔_; _⊓_)
open import Data.Product public
  using (proj₁; proj₂; ∃; ∄; ∃₂; _×_; _,_; _,′_; swap; curry; uncurry)
open import Data.String public
  using (String; Costring; toVec; toCostring; toList)
open import Data.Sum public
  using () renaming (_⊎_ to Either; inj₁ to left; inj₂ to right)
open import Data.Unit public using (⊤)
open import Data.Vec public using (Vec; []; _∷_; _∷ʳ_)

------------------------------------------------------------------------
-- Relations

open import Relation.Binary.Core public using (Decidable)
open import Relation.Binary.PropositionalEquality public
   using (_≡_; subst; subst₂; cong; cong₂; sym; refl; module ≡-Reasoning;
         trans; _≢_; proof-irrelevance; Extensionality)
open import Relation.Nullary public using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Type classes

open import Class.Append public
open import Class.Concat public
open import Class.DecEq public
open import Class.DecSetoid public
open import Class.DecTotalOrder public
open import Class.Drop public
open import Class.Eq public
open import Class.Foldl public
open import Class.Foldr public
open import Class.Functor public
open import Class.FromList public
open import Class.Length public
open import Class.Lines public
open import Class.ListLiteral public
open import Class.Map public
open import Class.Member public
open import Class.Monad public
open import Class.Null public
open import Class.Replicate public
open import Class.Reverse public
open import Class.Setoid public
open import Class.Show public
open import Class.StrictTotalOrder public
open import Class.Take public
open import Class.Unlines public
open import Class.ZipWith public

------------------------------------------------------------------------
-- Helper functions

charToℕ : Char → Maybe ℕ
charToℕ '0' = just 0
charToℕ '1' = just 1
charToℕ '2' = just 2
charToℕ '3' = just 3
charToℕ '4' = just 4
charToℕ '5' = just 5
charToℕ '6' = just 6
charToℕ '7' = just 7
charToℕ '8' = just 8
charToℕ '9' = just 9
charToℕ _   = nothing

stringToℕ' : List Char → (acc : ℕ) → Maybe ℕ
stringToℕ' []       acc = just acc
stringToℕ' (x ∷ xs) acc = charToℕ x >>= λ n → stringToℕ' xs $ 10 * acc + n

stringToℕ : String → Maybe ℕ
stringToℕ s = stringToℕ' (toList s) 0
