
-- Explicit Type Classes in Haskell

{-# LANGUAGE RankNTypes , ImpredicativeTypes #-}

module Control.ExplicitTC where

-- Monoid

data EMonoid a = EMonoid {
    mempty :: a,
    mappend :: a -> a -> a }

mconcat :: EMonoid a -> [a] -> a
mconcat (EMonoid mempty mappend) = foldr mappend mempty



-- Monoid Instances

listMonoid :: EMonoid [a]
listMonoid = EMonoid mempty mappend where
    mempty = []
    mappend = (++)



-- Monad

data EMonad m = EMonad {
    bind :: forall a b. m a -> (a -> m b) -> m b,
    return :: forall a. a -> m a }



-- Monad Instances

maybeMonad :: EMonad Maybe
maybeMonad = EMonad (>>=) return where
    Nothing >>= _ = Nothing
    Just a >>= f = f a
    return a = Just a

listMonad :: EMonad []
listMonad = EMonad (>>=) return where
    (>>=) = flip concatMap
    return a = [a]

writerMonad :: EMonoid w -> EMonad ((,) w)
writerMonad (EMonoid mempty mappend) = EMonad (>>=) return where
    return = (,) mempty
    (w, a) >>= f = let (w', a') = f a in (mappend w w', a')



