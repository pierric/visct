{- Identity monad, the trivial monad, 
 - cloning the standard library 'transformers' -}
module Identity(
    Identity,
    runIdentity,
  ) where

newtype Identity a = Identity { runIdentity :: a }

instance Functor Identity where
    fmap f m = Identity (f (runIdentity m))

instance Monad Identity where
    return a = Identity a
    m >>= k  = k (runIdentity m)
