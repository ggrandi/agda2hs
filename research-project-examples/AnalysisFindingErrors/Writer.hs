module AnalysisFindingErrors.Writer where

import Test.QuickCheck (Arbitrary(arbitrary, shrink))

newtype Writer w a = Writer'{runWriter :: (w, a)}
                       deriving (Show)

tell :: w -> Writer w ()
tell = Writer' . \ section -> (section, ())

instance (Eq w, Eq a) => Eq (Writer w a) where
    Writer' x == Writer' y = x == y

instance Functor (Writer w) where
    fmap f (Writer' x) = Writer' $ f <$> x

instance (Monoid w) => Applicative (Writer w) where
    pure = Writer' . pure
    Writer' mf <*> Writer' mx = Writer' $ mf <*> mx

instance (Monoid w) => Monad (Writer w) where
    Writer' x >>= k = Writer' $ x >>= (\ r -> runWriter r) . k

instance (Arbitrary w, Arbitrary a) => Arbitrary (Writer w a) where
    arbitrary = curry Writer' <$> arbitrary <*> arbitrary
    shrink (Writer' x) = Writer' <$> shrink x

