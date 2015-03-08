------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

module Foreign.Haskell where

-- A unit type.

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

open import Data.Nat

postulate
  Integer : Set
  #0      : Integer
  plusOne : Integer → Integer

{-# COMPILED_TYPE Integer Integer #-}
{-# COMPILED #0   (0 :: Integer)      #-}
{-# COMPILED plusOne \n -> n+1    #-}

toInteger : ℕ → Integer
toInteger zero = #0
toInteger (suc n) = plusOne (toInteger n)
