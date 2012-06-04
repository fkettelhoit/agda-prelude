module Class.Unlines where

open import Data.Char using (Char)
open import Data.List using (List)
open import Coinduction
open import Data.Colist using (Colist; []; _∷_; concat; map; _++_)
open import Data.String using (String; Costring; toList)
open import Function using (_∘_; _$_)
open import Data.List.NonEmpty using (List⁺; fromVec)
open import Data.Vec using (Vec; _∷ʳ_; fromList)

open import Level using (Level; suc)

record unlinesClass (F : Set → Set) (A : Set) : Set where
  field
    unlines : (F String) → A

open unlinesClass {{...}} public

unlinesInstanceList : unlinesClass List String
unlinesInstanceList = record { unlines = Data.String.unlines }

fromListr : ∀ {a} {A : Set a} → List A → A → List⁺ A
fromListr xs x = fromVec $ fromList xs ∷ʳ x

trim : Colist Char → Colist Char
trim [] = []
trim (x ∷ xs) with ♭ xs
...           | [] = []
...           | (y ∷ ys) = x ∷ (♯ trim (y ∷ ys))

unlinesColist : Colist String → Costring
unlinesColist l = concat $ map ((λ x → fromListr x '\n') ∘ toList) l

unlinesInstanceColist : unlinesClass Colist Costring
unlinesInstanceColist = record { unlines = unlinesColist }
