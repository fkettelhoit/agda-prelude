------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for Functors
------------------------------------------------------------------------

module Class.Functor where

open import Category.Functor using (RawFunctor; module RawFunctor)
open import Data.Maybe public using () renaming (functor to maybeFunctor)
open import Data.List using (List)
open import Data.Colist using (Colist)

open import Level using (Level)

------------------------------------------------------------------------
-- Type class

open RawFunctor {{...}} public

------------------------------------------------------------------------
-- Instances

functorInstanceList : {a : Level} → RawFunctor {a} (List {a})
functorInstanceList {a} = record { _<$>_ = λ f l → Data.List.map f l }

functorInstanceColist : {a : Level} → RawFunctor {a} (Colist {a})
functorInstanceColist {a} = record { _<$>_ = λ f l → Data.Colist.map f l }
