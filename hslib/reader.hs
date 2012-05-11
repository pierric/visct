module Reader(
    ReaderT,
    runReaderT,
    Reader,
    runReader,
    asks
  ) where

import Identity

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

instance (Functor m) => Functor (ReaderT r m) where
    fmap f  = mapReaderT (fmap f)

instance (Monad m) => Monad (ReaderT r m) where
    return   = ReaderT . const . return
    m >>= k  = ReaderT $ \ r -> do
        a <- runReaderT m r
        runReaderT (k a) r
    fail msg = ReaderT $ const (fail msg)

mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = ReaderT $ f . runReaderT m

asks :: (Monad m) => (r -> a) -> ReaderT r m a
asks f = ReaderT (return . f)

type Reader r = ReaderT r Identity

runReader m = runIdentity . runReaderT m

