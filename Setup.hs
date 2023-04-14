-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
import Data.Functor
import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.Types.HookedBuildInfo
import Distribution.Types.LocalBuildInfo
import Distribution.Types.PackageDescription
import Turtle

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks {
      postConf = \_ _ _ _ -> runMake
    , preBuild = \_ _ -> runMake >> pure emptyHookedBuildInfo
    }

runMake :: IO ()
runMake = procs "make" [] empty

-- runAgda :: IO ()
-- runAgda = procs "agda" ["--compile", "--ghc-dont-call-ghc", "--local-interfaces", "src/Main.lagda"] empty
