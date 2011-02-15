
import Data.Monoid
import Control.Monad

instance Monoid a => Monad ((,) a) where
    return a = (mempty, a)
    (r, a) >>= f = let (r', b) = f a in (mappend r r', b)

