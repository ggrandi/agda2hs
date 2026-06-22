module Vector where

import Numeric.Natural (Natural)

data Vec a = Nil
           | Cons a (Vec a)

mapV :: (a -> b) -> Vec a -> Vec b
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)

tailV :: Vec a -> Vec a
tailV (Cons x xs) = xs

len :: Vec a -> Natural
len Nil = 0
len (Cons _ xs) = 1 + len xs

instance (Eq a) => Eq (Vec a) where
    Nil == Nil = True
    Cons x xs == Cons y ys = x == y && xs == ys
    _ == _ = False

