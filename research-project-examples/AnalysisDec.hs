{-# LANGUAGE RankNTypes #-}
module AnalysisDec where

import Data.List (sort)

decIsAscending :: Ord a => [a] -> Bool
decIsAscending [] = True
decIsAscending [_] = True
decIsAscending (x : (y : xs)) = x <= y && decIsAscending (y : xs)

class ExtractSorted cont where
    extractSorted :: forall a . Ord a => cont a -> [a]

instance ExtractSorted [] where
    extractSorted = sort

prop_IsAscending_extractSorted (xs :: [Integer])
  = decIsAscending (extractSorted xs)

