
{-# LANGUAGE TypeFamilies #-}

data Zero
data Succ a

type family FixArray n a
type instance FixArray Zero a = ()
type instance FixArray (Succ n) a = (a, FixArray n a)

hoge :: FixArray (Succ (Succ (Succ (Succ Zero)))) Int
hoge = (1, (2, (3, (4, ()))))

