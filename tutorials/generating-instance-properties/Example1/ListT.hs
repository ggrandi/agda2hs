{-# LANGUAGE UndecidableInstances #-}

module Example1.ListT where

import Example1.Writer (Writer)
import Numeric.Natural (Natural)
import Test.QuickCheck (Arbitrary(arbitrary, shrink))


import Test.QuickCheck.Function (Fun(..))

newtype ListT m a = ListT'{runListT :: m [a]}

instance (Eq (m [a])) => Eq (ListT m a) where
    x == y = runListT x == runListT y

instance (Show (m [a])) => Show (ListT m a) where
    show = ("ListT (" ++) . (++ ")") . show . \ r -> runListT r

instance (Functor m) => Functor (ListT m) where
    fmap f (ListT' x) = ListT' $ (f <$>) <$> x

instance (Applicative m) => Applicative (ListT m) where
    pure = ListT' . pure . pure
    ListT' mf <*> ListT' mx = ListT' $ (<*>) <$> mf <*> mx

instance (Monad m) => Monad (ListT m) where
    m >>= k
      = ListT' $
          do a <- runListT m
             b <- mapM ((\ r -> runListT r) . k) a
             pure (concat b)

prop_leftIdentity (x :: Natural)
  (Fun _ (k :: Natural -> ListT (Writer String) Natural))
  = (return x >>= k) == k x
prop_rightIdentity (ma :: ListT (Writer String) Natural)
  = (ma >>= return) == ma
prop_associativity (ma :: ListT (Writer String) Natural)
  (Fun _ (f :: Natural -> ListT (Writer String) Natural))
  (Fun _ (g :: Natural -> ListT (Writer String) Natural))
  = do x <- ma
       f x >>= g
      == (ma >>= f >>= g)
prop_def_seq_bind (ma :: ListT (Writer String) Natural)
  (mb :: ListT (Writer String) Natural)
  = do ma
       mb
      ==
      do x <- ma
         mb
prop_def_pure_return (x :: Natural)
  = (pure x :: ListT (Writer String) Natural) == return x
prop_def_fmap_bind (Fun _ (f :: Natural -> Natural))
  (ma :: ListT (Writer String) Natural)
  = fmap f ma == (ma >>= return . f)
prop_def_zap_bind
  (mab :: ListT (Writer String) (Natural -> Natural))
  (ma :: ListT (Writer String) Natural)
  = (mab <*> ma) ==
      do f <- mab
         x <- ma
         return (f x)

instance (Arbitrary (m [a])) => Arbitrary (ListT m a) where
    arbitrary = ListT' <$> arbitrary
    shrink = (ListT' <$>) . shrink . \ r -> runListT r

