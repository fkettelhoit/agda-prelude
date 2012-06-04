module Class.Lines where

open import Class.Reverse
open import Class.FromList
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Coinduction
open import Data.Colist using (Colist; []; _∷_; concat; map; _++_)
open import Data.String using (String; Costring; toList)
open import Function using (_∘_; _$_)
open import Data.List.NonEmpty using (List⁺; fromVec)

open import Level using (Level)

record linesClass (A : Set) (F : Set → Set) : Set where
  field
    lines : A → (F String)

open linesClass {{...}} public

-- we need the maxLineLength to make sure the lines function terminates
-- not exactly perfect, but works
maxLineLength = 100000

linesCostring : Costring → Colist String
linesCostring xs = lines' maxLineLength xs []
  where lines' : ℕ → Costring -> List Char → Colist String
        lines' zero    xs          s = fromList (reverse s) ∷ ♯ lines' maxLineLength xs []
        lines' (suc n) ('\n' ∷ xs) s = fromList (reverse s) ∷ ♯ lines' maxLineLength (♭ xs) []
        lines' (suc n) (x ∷ xs)    s = lines' n (♭ xs) (x ∷ s)
        lines' (suc n) []          s = fromList (reverse s) ∷ ♯ []

lines2' : List Char → List Char → List String
lines2' acc [] = fromList (reverse acc) ∷ []
lines2' acc ('\n' ∷ xs) = fromList (reverse acc) ∷ lines2' [] xs
lines2' acc (x    ∷ xs) = lines2' (x ∷ acc) xs

trim2 : List Char → List Char → List Char
trim2 acc [] = reverse acc
trim2 acc ('\n' ∷ []) = reverse acc
trim2 acc (x ∷ xs) = trim2 (x ∷ acc) xs

lines2 : String → List String
lines2 = lines2' [] ∘ trim2 [] ∘ toList

linesInstanceString : linesClass String List
linesInstanceString = record { lines = lines2 }

linesInstanceCostring : linesClass Costring Colist
linesInstanceCostring = record { lines = linesCostring }
