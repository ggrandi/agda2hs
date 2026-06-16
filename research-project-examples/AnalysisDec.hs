{-# LANGUAGE RankNTypes #-}
module AnalysisDec where

import Data.List (sort)
import Numeric.Natural (Natural)

decIsAscending :: Ord a => [a] -> Bool
decIsAscending [] = True
decIsAscending [_] = True
decIsAscending (x : (y : xs)) = x <= y && decIsAscending (y : xs)

class ExtractSorted cont where
    extractSorted :: forall a . Ord a => cont a -> [a]

instance ExtractSorted [] where
    extractSorted = sort

prop_IsAscending_extractSorted (xs :: [Natural])
  = decIsAscending (extractSorted xs)

fun :: [[Natural]] -> Bool
fun xss = it (all (\ x -> length x == 10##) xss)

