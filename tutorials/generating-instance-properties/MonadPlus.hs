module MonadPlus where

import Alternative (Alternative)

class (Monad m, Alternative m) => MonadPlus m where

