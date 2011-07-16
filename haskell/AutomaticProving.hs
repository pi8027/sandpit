
module Main where

import Data.Char
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import Data.Attoparsec.Char8 as AP hiding (many)
import qualified Data.ByteString.Char8 as BS
import Control.Applicative
import Control.Monad.State
import Control.Arrow

-- Definition

data Term i = EVar i | EApp (Term i) (Term i) | EAbs i (Term i)
data Type i = TVar i | TFun (Type i) (Type i) deriving Show

data TermLevel = LambdaTermL | ApplyTermL | FactorTermL deriving (Eq, Ord)

-- Parser, Pretty Printer

getResToken :: String -> Parser ()
getResToken str = string (BS.pack str) >> many space >> return ()

typeP1, typeP2, typeParser :: Parser (Type String)
typeP1 = do
    t <- typeP2
    (getResToken "->" >> TFun t <$> typeP1) <|> return t
typeP2 =
    (TVar . BS.unpack <$> AP.takeWhile1 isAlpha <* many space) <|>
    (getResToken "(" *> typeP1 <* getResToken ")")
typeParser = many space *> typeP1 <* endOfInput

bracketPpr :: Bool -> ShowS -> ShowS
bracketPpr False shows = ('(' :) . shows . (')' :)
bracketPpr True shows = shows

termPpr :: (i -> ShowS) -> TermLevel -> Term i -> ShowS
termPpr f level (EVar i) = f i
termPpr f level (EApp t1 t2) =
    bracketPpr (level <= ApplyTermL) $
        termPpr f ApplyTermL t1 . (' ' :) . termPpr f FactorTermL t2
termPpr f level (EAbs i t) =
    bracketPpr (level <= LambdaTermL) $
        ("\\" ++) . f i . (" -> " ++) . termPpr f LambdaTermL t

-- Automatic Proving

destructType :: Type i -> ([Type i], i)
destructType (TVar i) = ([], i)
destructType (TFun t1 t2) = first (t1 :) $ destructType t2

intToStr :: Int -> String -> String
intToStr n s = if n < 26 then s' else intToStr ((n `div` 26) - 1) s' where
    s' = chr (ord 'a' + n `mod` 26) : s

proving :: Ord i =>
    [(Int, Type i)] -> Set.Set i -> Type i -> StateT Int [] (Term String)
proving env hist (TVar ident) | Set.member ident hist = lift []
proving env hist (TVar tident) = do
    (eident, (args, _)) <-
        lift $ filter ((tident ==) . snd . snd) $ map (second destructType) env
    Foldable.foldlM (\e t -> EApp e <$> proving env (Set.insert tident hist) t)
        (EVar (intToStr eident [])) args
proving env hist (TFun t1 t2) = do
    n <- get
    put (succ n) >> EAbs (intToStr n []) <$> proving ((n, t1) : env) hist t2

-- main

main :: IO ()
main = do
    contents <- BS.getContents
    case feed (parse typeParser contents) BS.empty of
        Done _ result -> mapM_ (putStrLn . flip (termPpr (++) LambdaTermL) "")
            (evalStateT (proving [] Set.empty result) 0)
        err -> print err

