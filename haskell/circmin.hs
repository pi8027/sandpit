
circmin :: Ord a => [a] -> a
circmin l = circmin' (tail l) (head l) 1 where
    circmin' l' v n = if and $ take n $ zipWith (==) l l'
        then v
        else circmin' (tail l') (min v (head l')) (succ n)

