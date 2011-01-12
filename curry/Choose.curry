
module Choose where

choose :: [a] -> a
choose (x:xs) = x
choose (x:xs) = choose xs

