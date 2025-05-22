module Main where

import System.IO
import Text.ParserCombinators.ReadP
import Data.Char

-- === Core Types ===
data Term = Var Int | Lam Term | App Term Term | Error
  deriving (Show, Read, Eq)

data TypedTerm = TVar Int | TLam TypedTerm Type | TApp TypedTerm TypedTerm
  deriving (Show, Read, Eq)

data Type = T String | Arrow Type Type
  deriving (Show, Read, Eq)

type Context = [(String, Type)]

-- === Utilities ===
shift :: Int -> Term -> Term
shift d t = f 0 t
  where f c v@(Var x) = if x >= c then Var (d + x) else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

subst :: Int -> Term -> Term -> Term
subst j s t = f 0 t
  where f c v@(Var x) = if j + c == x then shift c s else v
        f c (Lam t) = Lam $ f (c + 1) t
        f c (App t u) = App (f c t) (f c u)

beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t

eval_step :: Term -> Term
eval_step (App (Lam t) u) = beta u t
eval_step (App t u) = App (eval_step t) (eval_step u)
eval_step (Lam t) = Lam $ eval_step t
eval_step t = t

eval :: Term -> Term
eval t = if t == t' then t else eval t'
  where t' = eval_step t

eraseType :: TypedTerm -> Term
eraseType (TVar x) = Var x
eraseType (TLam t _) = Lam (eraseType t)
eraseType (TApp t1 t2) = App (eraseType t1) (eraseType t2)

unify :: Type -> Type -> Maybe ()
unify (Arrow t11 t12) (Arrow t21 t22) = do
  unify t11 t21
  unify t12 t22
unify t1 t2 = if t1 == t2 then Just () else Nothing

inferType :: TypedTerm -> Context -> Maybe Type
inferType (TVar x) ctx = lookupIndex x ctx
inferType (TLam t1 ty) ctx = do
  t1ty <- inferType t1 (("_", ty):ctx)
  Just (Arrow ty t1ty)
inferType (TApp t1 t2) ctx = do
  t1ty <- inferType t1 ctx
  t2ty <- inferType t2 ctx
  case t1ty of
    Arrow t' t'' -> if unify t' t2ty == Just () then Just t'' else Nothing
    _ -> Nothing

lookupIndex :: Int -> Context -> Maybe Type
lookupIndex i ctx = if i < length ctx then Just (snd (ctx !! i)) else Nothing

teval :: TypedTerm -> Context -> Term
teval t c = case inferType t c of
  Nothing -> Error
  Just _ -> eval $ eraseType t

-- === Parsing ===
type Parser a = ReadP a

symbol :: String -> Parser String
symbol s = skipSpaces >> string s <* skipSpaces

ident :: Parser String
ident = skipSpaces >> munch1 isAlpha

parseType :: Parser Type
parseType = chainr1 parseAtomicType (symbol "->" >> return Arrow)

parseAtomicType :: Parser Type
parseAtomicType =
      (T <$> ident)
  +++ between (symbol "(") (symbol ")") parseType

parseTypedTerm :: [String] -> Parser TypedTerm
parseTypedTerm ctx = parseApp ctx

parseApp :: [String] -> Parser TypedTerm
parseApp ctx = chainl1 (parseAtom ctx) (return TApp)

parseAtom :: [String] -> Parser TypedTerm
parseAtom ctx = parseLam ctx +++ parseVar ctx +++ parseParen ctx

parseVar :: [String] -> Parser TypedTerm
parseVar ctx = do
  x <- ident
  case lookup x (zip ctx [0..]) of
    Just i -> return $ TVar i
    Nothing -> pfail

parseLam :: [String] -> Parser TypedTerm
parseLam ctx = do
  symbol "\\"
  x <- ident
  symbol ":"
  ty <- parseTypeWithSpaces
  symbol "."
  body <- parseTypedTerm (x:ctx)
  return $ TLam body ty

-- parsira tip i uklanja razmake sa obe strane
parseTypeWithSpaces :: Parser Type
parseTypeWithSpaces = skipSpaces *> parseType <* skipSpaces

parseParen :: [String] -> Parser TypedTerm
parseParen ctx = between (symbol "(") (symbol ")") (parseTypedTerm ctx)

parseFull :: String -> Either String TypedTerm
parseFull input = case readP_to_S (parseTypedTerm [] <* skipSpaces <* eof) input of
  [(res, "")] -> Right res
  _ -> Left "Ne mogu parsirati izraz."

-- === REPL ===
main :: IO ()
main = do
  putStrLn "Type :q to quit."
  repl []

repl :: Context -> IO ()
repl ctx = do
  putStr ">>> "
  hFlush stdout
  input <- getLine
  if input == ":q" then putStrLn "Bye!" else do
    case parseFull input of
      Left err -> putStrLn err
      Right t -> do
        let result = teval t ctx
        putStrLn ("Evaluated: " ++ show result)
    repl ctx
