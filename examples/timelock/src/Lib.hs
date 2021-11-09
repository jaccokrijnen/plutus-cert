--
-- Necessary language extensions for the Plutus Tx compiler to work.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Lib where

import qualified Language.PlutusCore.Builtins as PLC
import qualified Language.PlutusCore.Universe as PLC
-- Main Plutus Tx module.
import           Language.PlutusTx
-- Additional support for lifting.
import           Language.PlutusTx.Lift
-- Builtin functions.
import           Language.PlutusTx.Builtins
-- The Plutus Tx Prelude, discussed further below.
import           Language.PlutusTx.Prelude

-- integerIdentity :: CompiledCode (Integer -> Integer)
-- integerIdentity = $$(compile [|| \(x:: Integer) -> x ||])
--
--
--
-- {- Functions which will be used in Plutus Tx programs should be marked
--   with GHC’s 'INLINABLE' pragma. This is usually necessary for
--   non-local functions to be usable in Plutus Tx blocks, as it instructs
--   GHC to keep the information that the Plutus Tx compiler needs. While
--   you may be able to get away with omitting it, it is good practice to
--   always include it. -}
-- {-# INLINABLE plusOne #-}
-- plusOne:: Integer -> Integer
-- {- 'addInteger' comes from 'Language.PlutusTx.Builtins', and is
--   mapped to the builtin integer addition function in Plutus Core. -}
-- plusOne x = x `addInteger` 1
--
-- {-# INLINABLE myProgram #-}
-- myProgram :: Integer
-- myProgram =
--     let
--         -- Local functions do not need to be marked as 'INLINABLE'.
--         plusOneLocal :: Integer -> Integer
--         plusOneLocal x = x `addInteger` 1
--
--         localTwo = plusOneLocal 1
--         externalTwo = plusOne 1
--     in localTwo `addInteger` externalTwo
--
-- functions :: CompiledCode Integer
-- functions = $$(compile [|| myProgram ||])


-- | Either a specific end date, or "never".
data EndDate = Fixed Integer | Never

-- | Check whether a given time is past the end date.
pastEnd :: CompiledCode (EndDate -> Integer -> Bool)
pastEnd = $$(compile [|| \(end::EndDate) (current::Integer) ->
    let remove = Fixed 3
        {-# NOINLINE remove#-}
        keep   = case Never of {Never -> False;_ -> True}
        {-# NOINLINE keep#-}
    in case end of
    Fixed n -> n `lessThanEqInteger` current
    Never   -> keep
  ||])

-- Experimenting with what let-bindings become strict/non-strcit
-- in PIR.
--
-- thunkrec :: CompiledCode (EndDate -> Integer -> Bool)
-- thunkrec = $$(compile [|| \(end::EndDate) (current::Integer) ->
--     let rec_loops :: Bool = rec_loops
--
--         myNil :: [a]
--         myNil = []
--
--         {-# NOINLINE myTrue#-}
--         myTrue = True
--
--         {-# NOINLINE idBool#-}
--         idBool :: Bool -> Bool
--         idBool = idBool
--
--         {-# NOINLINE rec_loops #-}
--         mymap :: (a -> b) -> [a] -> [b]
--         mymap f [] = []
--         mymap f (x:xs) = f x : mymap f xs
--
--         head :: [a] -> a
--         head (x : xs) = x
--         head [] = Language.PlutusTx.Builtins.error ()
--     in head (idBool myTrue : mymap (\x -> rec_loops) [1,2,3])
--     ||])
