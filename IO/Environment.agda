module IO.Environment where

import IO
open import IO.Primitive as Prim
open import Data.Colist
open import Data.String

{-# IMPORT System.Environment #-}

postulate
  getArgsPrim : Prim.IO (Colist String)
  getProgNamePrim : Prim.IO String

{-# COMPILED getArgsPrim System.Environment.getArgs #-}
{-# COMPILED getProgNamePrim System.Environment.getProgName #-}

getArgs : IO.IO (Colist String)
getArgs = IO.lift getArgsPrim

getProgName : IO.IO String
getProgName = IO.lift getProgNamePrim
