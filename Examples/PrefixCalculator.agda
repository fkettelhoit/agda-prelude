{-# OPTIONS --sized-types --show-implicit #-}

module Examples.PrefixCalculator where

open import Prelude hiding (List; []; _∷_)

infixr 5 _∷_
data List {a : Level} (A : Set a) : {size : Size} → Set a where
  []  : {i : Size} →                  List A {↑ i}
  _∷_ : {i : Size} → A → List A {i} → List A {↑ i}

toCustomList : {A : Set} → Prelude.List A → List A
toCustomList Prelude.[]         = []
toCustomList (Prelude._∷_ x xs) = x ∷ (toCustomList xs)

toOrigList : {A : Set} → List A → Prelude.List A
toOrigList []       = Prelude.[]
toOrigList (x ∷ xs) = Prelude._∷_ x (toOrigList xs)

reverse′ : ∀ {a} {A : Set a} → List A → List A → List A
reverse′ acc []       = acc
reverse′ acc (x ∷ xs) = reverse′ (x ∷ acc) xs

reverseInstanceCustomList : {a : Level} → reverseClass ⊤ (λ A n → List A)
reverseInstanceCustomList {a} = record { reverse = reverse′ {a} [] }

data Token : Set where
  lPar   : Token
  rPar   : Token
  symbol : String → Token

infixr 4 _∷T_
_∷T_ : List Char → List Token → List Token
[]  ∷T tokens = tokens
tok ∷T tokens = (symbol ((fromList ∘ toOrigList ∘ reverse) tok)) ∷ tokens

tokenize′ : List Char → List Char → List Token
tokenize′ tok ('(' ∷ rest) = tok ∷T (lPar ∷ (tokenize′ [] rest))
tokenize′ tok (')' ∷ rest) = tok ∷T rPar ∷ (tokenize′ [] rest)
tokenize′ tok (' ' ∷ rest) = tok ∷T (tokenize′ [] rest)
tokenize′ tok (c   ∷ rest) = tokenize′ (c ∷ tok) rest
tokenize′ tok []           = tok ∷T []

tokenize : List Char → List Token
tokenize = tokenize′ []

data SExp : Set where
  atom : String → SExp
  nil  : SExp
  cons : SExp → SExp → SExp

_▷_ : SExp → SExp → SExp
(atom x)    ▷ y = (cons (atom x) y)
nil         ▷ y = (cons y nil)
(cons x xs) ▷ y = (cons x (xs ▷ y))

Error = String

parse′ : {i : Size} → SExp → List Token {i} → Either (SExp × (List Token {i})) Error
parse′ acc [] = right "unexpected end of expression"
parse′ acc (lPar ∷ xs) with parse′ nil xs
...                    | right e = right e
...                    | left (exp , []) = left $ acc ▷ exp , []
...                    | left (exp , rest) = parse′ (acc ▷ exp) rest
parse′ acc (rPar ∷ rest) = left (acc , rest)
parse′ acc (symbol y ∷ rest) = parse′ (acc ▷ (atom y)) rest

parse : List Token → Either SExp Error
parse []                        = right "invalid expression"
parse (symbol y ∷ [])           = left (atom y)
parse (symbol y ∷ rest)         = right "invalid expression"
parse (lPar ∷ rest) with parse′ nil rest
...           | right e = right e
...           | left (exp , []) = left exp
...           | left (exp , _)  = right "invalid expression"
parse (rPar ∷ rest)             = right "invalid expression"

eval : SExp → Either ℕ Error
eval (atom x) with stringToℕ x
...           | just n = left n
...           | nothing = right $ "not a number: " ++ x
eval (cons (atom op) (cons a (cons b nil))) with eval a | eval b | op
... | left x  | left y  | "+" = left (x + y)
... | left x  | left y  | "-" = left (x ∸ y)
... | left x  | left y  | "*" = left (x * y)
... | right e | _       | _   = right e
... | _       | right e | _   = right e
... | _       | _       | e   = right $ "unknown operator '" ++ e ++ "'"
eval _ = right "invalid expression"

repl : String → String
repl s with (parse ∘ tokenize ∘ toCustomList ∘ toList) s
repl s | left exp with eval exp
repl s | left exp | left n  = "= " ++ show n
repl s | left exp | right e = "error: " ++ e
repl s | right e            = "error: " ++ e

main′ : _
main′ = ♯ getContents ∞>>= λ input →
        ♯ (putStrLn∞ ∘ unlines ∘ (map repl) ∘ lines) input

main : _
main = run main′
