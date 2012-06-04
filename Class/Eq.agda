------------------------------------------------------------------------
-- The Agda standard library
--
-- A type class for _==_
------------------------------------------------------------------------

module Class.Eq where

open import Data.Char   renaming (_==_ to _==Char_)
open import Data.String renaming (_==_ to _==String_)

open import Data.Bool

------------------------------------------------------------------------
-- Type class

record ==Class (A : Set) : Set where
  field
    _==_ : A → A → Bool

open ==Class {{...}} public

------------------------------------------------------------------------
-- Instances

==InstanceChar : ==Class Char
==InstanceChar = record { _==_ = _==Char_ }

==InstanceString : ==Class String
==InstanceString = record { _==_ = _==String_ }
