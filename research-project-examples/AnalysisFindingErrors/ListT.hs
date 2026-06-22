{-# LANGUAGE UndecidableInstances #-}

module AnalysisFindingErrors.ListT where

import AnalysisFindingErrors.Writer (Writer)
import Test.QuickCheck (Arbitrary(arbitrary, shrink))


import Test.QuickCheck.Function (Fun(..))

newtype ListT m a = ListT'{runListT :: m [a]}

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

prop_leftIdentity (x :: Integer)
  (Fun _ (k :: Integer -> ListT (Writer String) Integer))
  = (return x >>= k) == k x
prop_rightIdentity (ma :: ListT (Writer String) Integer)
  = (ma >>= return) == ma
prop_associativity (ma :: ListT (Writer String) Integer)
  (Fun _ (f :: Integer -> ListT (Writer String) Integer))
  (Fun _ (g :: Integer -> ListT (Writer String) Integer))
  = do x <- ma
       f x >>= g
      == (ma >>= f >>= g)
prop_def_seq_bind (ma :: ListT (Writer String) Integer)
  (mb :: ListT (Writer String) Integer)
  = do ma
       mb
      ==
      do x <- ma
         mb
prop_def_pure_return (x :: Integer)
  = (pure x :: ListT (Writer String) Integer) == return x
prop_def_fmap_bind (Fun _ (f :: Integer -> Integer))
  (ma :: ListT (Writer String) Integer)
  = fmap f ma == (ma >>= return . f)
prop_def_zap_bind
  (mab :: ListT (Writer String) (Integer -> Integer))
  (ma :: ListT (Writer String) Integer)
  = (mab <*> ma) ==
      do f <- mab
         x <- ma
         return (f x)

instance (Arbitrary (m [a])) => Arbitrary (ListT m a) where
    arbitrary = ListT' <$> arbitrary
    shrink (ListT' x) = ListT' <$> shrink x

instance (Eq (m [a])) => Eq (ListT m a) where
    x == y = runListT x == runListT y

