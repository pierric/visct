{- MonadTras type class, abstract operation on monad nesting. -}
module Trans where

class MonadTrans t where
    lift :: Monad m => m a -> t m a
