------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for show
------------------------------------------------------------------------

module Class.Show where

open import Data.Bool using (Bool)
open import Data.Bool.Show renaming (show to showBool)
import Data.Bin as Bin; open Bin using (Bin)
open import Data.Char using (Char)
import Data.DifferenceNat as Diff; open Diff using (Diffℕ)
open import Data.Digit using (Digit; Bit)
  renaming (showDigit to showDigitAsChar)
open import Data.Empty using (⊥)
import Data.Fin as Fin; open Fin using (Fin)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Rational using (ℚ)
open import Data.Sign using (Sign)
open import Data.String using (String; fromList; _++_)
open import Data.Unit using (⊤)

open import Data.List using (List; [_]; _∷_; [])
open import Function
open import Level using (Level)

open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Type class

record showClass {a} (A : Set a) : Set a where
  field
    show : A → String

open showClass {{...}} public

------------------------------------------------------------------------
-- Instances

showInstanceBool : showClass Bool
showInstanceBool = record { show = showBool }

showInstanceℕ : showClass ℕ
showInstanceℕ = record { show = showℕ }

showBin : Bin → String
showBin = showℕ ∘ Bin.toℕ

showInstanceBin : showClass Bin
showInstanceBin = record { show = showBin }

showChar : Char → String
showChar x = fromList [ x ]

showInstanceChar : showClass Char
showInstanceChar = record { show = showChar }

showDiffℕ : Diffℕ → String
showDiffℕ = showℕ ∘ Diff.toℕ

showInstanceDiffℕ : showClass Diffℕ
showInstanceDiffℕ = record { show = showDiffℕ }

showDigit : {base : ℕ}{{base≤16 : True (base ≤? 16)}} → Digit base → String
showDigit {base}{{proof}} x = fromList [ (showDigitAsChar {base}{proof} x) ]

showInstanceDigit :  {base : ℕ}{{base≤16 : True (base ≤? 16)}} →
                     showClass (Digit base)
showInstanceDigit = record { show = showDigit }

show⊥ : ⊥ → String
show⊥ x = "⊥"

showInstance⊥ : showClass ⊥
showInstance⊥ = record { show = show⊥ }

showFin : {n : ℕ} → Fin n → String
showFin = showℕ ∘ Fin.toℕ

showInstanceFin : {n : ℕ} → showClass (Fin n)
showInstanceFin = record { show = showFin }

showℤ : ℤ → String
showℤ (Data.Integer.-[1+_] n) = "-" ++ showℕ (suc n)
showℤ (Data.Integer.+_ n) = showℕ n

showInstanceℤ : showClass ℤ
showInstanceℤ = record { show = showℤ }

showℚ : ℚ → String
showℚ n = ((showℤ ∘ ℚ.numerator) n) ++ "/" ++ ((showℤ ∘ ℚ.denominator) n)

showInstanceℚ : showClass ℚ
showInstanceℚ = record { show = showℚ }

showSign : Sign → String
showSign Data.Sign.+ = "+"
showSign Data.Sign.- = "-"

showInstanceSign : showClass Sign
showInstanceSign = record { show = showSign }

showInstanceString : showClass String
showInstanceString = record { show = \ x → x }

showUnit : ⊤ → String
showUnit x = "⊤"

showInstanceUnit : showClass ⊤
showInstanceUnit = record { show = showUnit }

------------------------------------------------------------------------
-- Collections

showList' : {a : Level} {A : Set a} {{s : showClass A}} → List A → String
showList' [] = "]"
showList' (x ∷ xs) = ", " ++ show x ++ (showList' xs)

showList : {a : Level} {A : Set a} {{s : showClass A}} → List A → String
showList [] = "[]"
showList (x ∷ xs) = "[" ++ show x ++ showList' xs

-- does not work with the current instance search:

-- showInstanceList : {a : Level} {A : Set a} {{s : showClass A}} →
--                    showClass (List A)
-- showInstanceList {a} {A} {{s}} = record { show = showList {a} {A} {{s}} }

-- test : String
-- test = show ('a' ∷ [])
