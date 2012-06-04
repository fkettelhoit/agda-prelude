module Examples.TabsToSpaces where

open import Prelude

tabsToSpaces′ : (spaces : ℕ) → List Char → List Char
tabsToSpaces′ n [] = []
tabsToSpaces′ n (x ∷ xs) with x
...                      | '\t' = (replicate n ' ') ++ (tabsToSpaces′ n xs)
...                      | _    = x ∷ tabsToSpaces′ n xs

tabsToSpaces : (spaces : ℕ) → String → String
tabsToSpaces n s = fromList $ tabsToSpaces′ n $ toList s

takeExactly : ∀ {a} {A : Set a} (n : ℕ) → Colist A → Maybe (Vec A n)
takeExactly zero    []       = just []
takeExactly zero    l        = nothing
takeExactly (suc n) []       = nothing
takeExactly (suc n) (x ∷ xs) = _∷_ x <$> takeExactly n (♭ xs)

-- A variant of Data.Maybe.maybe′ with argument ordering suited for long code
try_error?_ok?_ : ∀ {a b} {A : Set a}{B : Set b} → Maybe A → B → (A → B) → B
try (just x) error? error ok? ok = ok x
try nothing  error? error ok? ok = error

main′ : IO ⊤
main′ = ♯ getArgs ∞>>= λ args →
  try    takeExactly 3 args
  error? ♯(putStrLn $ "exactly 3 arguments required:\n"
                       ++ "    1. input file\n"
                       ++ "    2. output file\n"
                       ++ "    3. number of spaces")
  ok?    λ { (infile ∷ outfile ∷ numspc ∷ []) →
              try    stringToℕ numspc
              error? ♯(putStrLn "The third argument needs to be a number!")
              ok?    λ n → 
                     ♯(♯ (readFiniteFile infile) ∞>>= λ input → 
                       ♯ (writeFile outfile ∘ unlines ∘
                          map (tabsToSpaces n) ∘ lines) input)
           }

main : _
main = run main′
