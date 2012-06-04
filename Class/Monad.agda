------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for Monads
------------------------------------------------------------------------

module Class.Monad where

open import Category.Monad using (RawMonad; module RawMonad)
open import Data.Maybe public using () renaming (monad to MaybeMonad)
open import Data.List public using () renaming (monad to ListMonad)

open RawMonad {{...}} public hiding (zipWith; _<$>_; _<$_)
