
module Split where

import Control.Monad
import Control.Applicative

--split :: [a] -> [[[a]]]
--split [] = return []
--split (x:xs) = split xs >>= f where
--    f [] = return [[x]]
--    f yss@(y:ys) = [[x]:yss, (x:y):ys]

--split :: [a] -> [[[a]]]
--split [] = return []
--split (x:xs) = let xss = split xs in (xss >>= f) ++ (xss >>= g) where
--    f yss = return $ [x]:yss
--    g (y:ys) = [(x:y):ys]
--    g _ = []

--split :: [a] -> [[[a]]]
--split [] = return []
--split (x:xs) = [r | f <- [return . ([x]:), f'], ys <- split xs, r <- f ys] where
--    f' (y:ys) = [(x:y):ys]
--    f' _ = []

split :: [a] -> [[[a]]]
split [] = return []
split (x:xs) = join $ [return . ([x]:), f'] <*> split xs where
    f' (y:ys) = [(x:y):ys]
    f' _ = []

