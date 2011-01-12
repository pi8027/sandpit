
module Split where

split :: [a] -> [[a]]
split l | foldr (\a@(_:_) b -> a++b) [] r =:= l = r where r free

