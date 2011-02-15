
module Functor where

import Prelude ()


class Functor f where
    map :: (a -> b) -> f a -> f b


class Functor f => Pointed f where
    return :: a -> f a

class Functor f => FunctorApply f where
    (<*>) :: f (a -> b) -> f a -> f b

class (Pointed f, FunctorApply f) => Applicative f

class Applicative f => Alternative f where
    empty :: f a
    (<|>) :: f a -> f a -> f a

class Applicative m => Monad m where
    (>>=) :: m a -> (a -> m b) -> m b

class (Alternative m, Monad m) => MonadPlus m


class Functor f => Copointed f where
    extract :: f a -> a

