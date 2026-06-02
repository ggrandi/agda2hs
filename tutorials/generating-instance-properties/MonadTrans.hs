{-# LANGUAGE RankNTypes #-}
module MonadTrans where

class MonadTrans t where
    lift :: forall a m . Monad m => m a -> t m a

