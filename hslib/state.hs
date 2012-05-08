module State(
    StateT,
    runStateT,
    evalStateT,
    get,
    put
  ) where

import Trans

newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }

instance (Functor m) => Functor (StateT s m) where
    fmap f m = StateT $ \ s ->
        fmap (\ ~(a, s') -> (f a, s')) $ runStateT m s

instance (Monad m) => Monad (StateT s m) where
    return a = state $ \s -> (a, s)
    m >>= k  = StateT $ \s -> do
        ~(a, s') <- runStateT m s
        runStateT (k a) s'
    fail str = StateT $ \_ -> fail str        

instance MonadTrans (StateT s) where
    lift m = StateT $ \s -> do
        a <- m
        return (a, s)    

evalStateT :: (Monad m) => StateT s m a -> s -> m a
evalStateT m s = do
    ~(a, _) <- runStateT m s
    return a

state :: Monad m => (s -> (a, s)) -> StateT s m a
state f = StateT (return . f)

get :: (Monad m) => StateT s m s
get = state $ \s -> (s, s)

put :: (Monad m) => s -> StateT s m ()
put s = state $ \_ -> ((), s)
