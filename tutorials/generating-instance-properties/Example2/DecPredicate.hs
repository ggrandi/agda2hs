{-# LANGUAGE RankNTypes #-}
module Example2.DecPredicate where

import Data.List (sort)
import Numeric.Natural (Natural)

decIsAscending :: Ord a => [a] -> Bool
decIsAscending [] = True
decIsAscending [x] = True
decIsAscending (x : (y : xs)) = x <= y && decIsAscending (y : xs)

class Sortable cont where
    ascendingList :: forall a . Ord a => cont a -> [a]

instance Sortable [] where
    ascendingList = sort

prop_IsAscending_ascendingList (xs :: [Natural])
  = decIsAscending (ascendingList xs)

fun :: [[Natural]] -> Bool
fun xs = eqInt (length xs) 1

