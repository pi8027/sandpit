
import Data.Functor
import Control.Arrow

permutations' :: [a] -> [[a]]
permutations' [] = [[]]
permutations' l = [x:ys | (x,xs) <- f l, ys <- permutations' xs]
    where f [] = []
          f (x:xs) = (x,xs):[(y,x:ys) | (y,ys) <- f xs]

