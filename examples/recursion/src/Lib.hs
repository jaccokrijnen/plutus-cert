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

pastEnd :: CompiledCode (Integer -> Bool)
pastEnd = $$(compile [|| \(y :: Integer) ->
    let
        z = addInteger y w
        w = addInteger y z
    in lessThanEqInteger z w
  ||])
