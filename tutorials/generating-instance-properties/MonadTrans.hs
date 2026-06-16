{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module MonadTrans where

class (Monad m, Monad (t m)) => MonadTrans m t where
  lift :: forall a. m a -> t m a
