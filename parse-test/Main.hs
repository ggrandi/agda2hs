module Main (main) where

import Control.Monad
import Language.Haskell.Exts.Parser
import Numeric.Natural (Natural)

main :: IO ()
main = getContents >>= print . (void <$>) . parseModule
