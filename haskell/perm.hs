import Control.Monad
import System.IO

splits :: [a] -> [([a], a, [a])]
splits [] = []
splits (x : xs) = ([], x, xs) : [(x : is, y, ts) | (is, y, ts) <- splits xs]

perm :: [a] -> [[a]]
perm [] = [[]]
perm xs = [y : ys | (is, y, ts) <- splits xs, ys <- perm (is ++ ts)]

measure :: [Int] -> Int
measure xs = sum [(n - m) * (n - m) | (n, m) <- zip xs [0..]]

enumNext :: [Int] -> [[Int]]
enumNext [] = []
enumNext (x : xs) =
  [y : (is ++ [x] ++ ts) | (is, y, ts) <- splits xs, y < x] ++
  map (x :) (enumNext xs)

main = do
  putStrLn "digraph perm {"
  forM_ (perm [0..5]) $ \p -> do
    putStrLn $ (p >>= \n -> "_" ++ show n) ++ "[label=\"" ++ show p ++ ", " ++ show (measure p) ++ "\"];"
    forM_ (enumNext p) $ \np -> do
      putStrLn $ (p >>= \n -> "_" ++ show n) ++ " -> " ++ (np >>= \n -> "_" ++ show n) ++ ";"
      if measure np < measure p then return () else putStrLn "error"
  putStrLn "}"
