{- Writer monad, the computation outputing something, 
 - cloning the standard library 'transformers' -}
module Writer(
    WriterT,
    runWriterT,
    tell
  ) where

import Data.Monoid
import Trans

newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }

instance (Functor m) => Functor (WriterT w m) where
    fmap f = mapWriterT $ fmap $ \ ~(a, w) -> (f a, w)

instance (Monoid w, Monad m) => Monad (WriterT w m) where
    return a = writer (a, mempty)
    m >>= k  = WriterT $ do
        ~(a, w)  <- runWriterT m
        ~(b, w') <- runWriterT (k a)
        return (b, w `mappend` w')
    fail msg = WriterT $ fail msg

instance (Monoid w) => MonadTrans (WriterT w) where
    lift m = WriterT $ do
        a <- m
        return (a, mempty)

writer :: Monad m => (a, w) -> WriterT w m a
writer = WriterT . return

mapWriterT :: (m (a, w) -> n (b, w')) -> WriterT w m a -> WriterT w' n b
mapWriterT f m = WriterT $ f (runWriterT m)

tell :: (Monoid w, Monad m) => w -> WriterT w m ()
tell w = writer ((), w)    
