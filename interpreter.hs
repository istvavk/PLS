module Main where

import System.IO
import Text.ParserCombinators.ReadP
import Data.Char

-- === Core Types ===
data Term
  = Var Int
  | Lam Term
  | App Term Term
  | IntLit Int
  | Add Term Term
  | Mul Term Term
  | BoolLit Bool
  | And Term Term
  | Or Term Term
  | Not Term
  | Nil
  | Cons Term Term
  deriving (Show, Read, Eq)

data TypedTerm
  = TVar String
  | TLam String Type TypedTerm
  | TApp TypedTerm TypedTerm
  | TIntLit Int
  | TAdd TypedTerm TypedTerm
  | TMul TypedTerm TypedTerm
  | TBoolLit Bool
  | TAnd TypedTerm TypedTerm
  | TOr TypedTerm TypedTerm
  | TNot TypedTerm
  | TNil Type
  | TCons TypedTerm TypedTerm
  deriving (Show, Read, Eq)

data Type
  = TInt
  | TBool
  | TFun Type Type
  | TList Type
  deriving (Show, Read, Eq)

type Env = [(String, TypedTerm)]
type Context = [(String, Type)]

-- === Evaluation ===

erase :: TypedTerm -> Term
erase = erase' []
  where
    erase' env (TVar x) =
      case lookup x (zip env [0..]) of
        Just i  -> Var i
        Nothing -> error ("Unbound variable in erase: " ++ x)
    erase' env (TLam x _ t) = Lam (erase' (x:env) t)
    erase' env (TApp t1 t2) = App (erase' env t1) (erase' env t2)
    erase' env (TIntLit n) = IntLit n
    erase' env (TAdd t1 t2) = Add (erase' env t1) (erase' env t2)
    erase' env (TMul t1 t2) = Mul (erase' env t1) (erase' env t2)
    erase' env (TBoolLit b) = BoolLit b
    erase' env (TAnd t1 t2) = And (erase' env t1) (erase' env t2)
    erase' env (TOr t1 t2) = Or (erase' env t1) (erase' env t2)
    erase' env (TNot t) = Not (erase' env t)
    erase' env (TNil _) = Nil
    erase' env (TCons h t) = Cons (erase' env h) (erase' env t)


shift :: Int -> Term -> Term
shift d = go 0
  where
    go c (Var x)     = Var (if x >= c then x + d else x)
    go c (Lam t)     = Lam (go (c + 1) t)
    go c (App t u)   = App (go c t) (go c u)
    go _ (IntLit n)  = IntLit n
    go c (Add t u)   = Add (go c t) (go c u)
    go c (Mul t u)   = Mul (go c t) (go c u)
    go _ (BoolLit b) = BoolLit b
    go c (And t u)   = And (go c t) (go c u)
    go c (Or t u)    = Or (go c t) (go c u)
    go c (Not t)     = Not (go c t)
    go _ Nil         = Nil
    go c (Cons h t)  = Cons (go c h) (go c t)

subst :: Int -> Term -> Term -> Term
subst j s = go 0
  where
    go c (Var x)     = if x == j + c then shift c s else Var x
    go c (Lam t)     = Lam (go (c + 1) t)
    go c (App t u)   = App (go c t) (go c u)
    go _ (IntLit n)  = IntLit n
    go c (Add t u)   = Add (go c t) (go c u)
    go c (Mul t u)   = Mul (go c t) (go c u)
    go _ (BoolLit b) = BoolLit b
    go c (And t u)   = And (go c t) (go c u)
    go c (Or t u)    = Or (go c t) (go c u)
    go c (Not t)     = Not (go c t)
    go _ Nil         = Nil
    go c (Cons h t)  = Cons (go c h) (go c t)

beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t

eval_step :: Term -> Term
eval_step (App (Lam t) u) = eval_step (beta (eval_step u) t)
eval_step (App t u) =
  case eval_step t of
    Lam t' -> eval_step (App (Lam t') (eval_step u))
    t'     -> App t' (eval_step u)
eval_step (Lam t) = Lam (eval_step t)

-- Aritmeticke operacije
eval_step (Add (IntLit a) (IntLit b)) = IntLit (a + b)
eval_step (Add t u) = case (eval_step t, eval_step u) of
  (IntLit a, IntLit b) -> IntLit (a + b)
  (t', u')             -> Add t' u'
eval_step (Mul (IntLit a) (IntLit b)) = IntLit (a * b)
eval_step (Mul t u) = case (eval_step t, eval_step u) of
  (IntLit a, IntLit b) -> IntLit (a * b)
  (t', u')             -> Mul t' u'
  
-- Boolean
eval_step (And (BoolLit a) (BoolLit b)) = BoolLit (a && b)
eval_step (And t u) = case (eval_step t, eval_step u) of
  (BoolLit a, BoolLit b) -> BoolLit (a && b)
  (t', u')               -> And t' u'
eval_step (Or (BoolLit a) (BoolLit b)) = BoolLit (a || b)
eval_step (Or t u) = case (eval_step t, eval_step u) of
  (BoolLit a, BoolLit b) -> BoolLit (a || b)
  (t', u')               -> Or t' u'
eval_step (Not (BoolLit a)) = BoolLit (not a)
eval_step (Not t) = Not (eval_step t)

-- Liste
eval_step Nil = Nil
eval_step (Cons h t) = Cons (eval_step h) (eval_step t)
eval_step t = t

eval :: Term -> Term
eval t = let t' = eval_step t in if t == t' then t else eval t'

-- === Provjera tipova ===

infer :: Context -> TypedTerm -> Maybe Type
infer ctx (TVar x) = lookup x ctx
infer ctx (TLam x ty t) = do
  tyBody <- infer ((x, ty):ctx) t
  return $ TFun ty tyBody
infer ctx (TApp t1 t2) = do
  TFun a b <- infer ctx t1
  a' <- infer ctx t2
  if a == a' then return b else Nothing
infer _ (TIntLit _) = Just TInt
infer ctx (TAdd a b) = do
  TInt <- infer ctx a
  TInt <- infer ctx b
  return TInt
infer ctx (TMul a b) = do
  TInt <- infer ctx a
  TInt <- infer ctx b
  return TInt
infer _ (TBoolLit _) = Just TBool
infer ctx (TAnd a b) = do
  TBool <- infer ctx a
  TBool <- infer ctx b
  return TBool
infer ctx (TOr a b) = do
  TBool <- infer ctx a
  TBool <- infer ctx b
  return TBool
infer ctx (TNot a) = do
  TBool <- infer ctx a
  return TBool
infer _ (TNil ty) = Just (TList ty)
infer ctx (TCons h t) = do
  hty <- infer ctx h
  TList tty <- infer ctx t
  if hty == tty then return (TList hty) else Nothing

-- === Parser ===

type Parser a = ReadP a

symbol :: String -> Parser String
symbol s = skipSpaces >> string s <* skipSpaces

ident :: Parser String
ident = skipSpaces >> munch1 isAlpha

parseType :: Parser Type
parseType = chainr1 parseTypeAtom (symbol "->" >> return TFun)

parseTypeAtom :: Parser Type
parseTypeAtom =
      (symbol "Int" >> return TInt)
  +++ (symbol "Bool" >> return TBool)
  +++ (do
          symbol "["
          ty <- parseType
          symbol "]"
          return (TList ty))
  +++ between (symbol "(") (symbol ")") parseType

parseExpr :: [String] -> Parser TypedTerm
parseExpr ctx = parseLam ctx +++ parseOp ctx

parseOp :: [String] -> Parser TypedTerm
parseOp ctx = chainl1 (parseApp ctx) opParser
  where
    opParser =   (symbol "+"  >> return TAdd)
             +++ (symbol "*"  >> return TMul)
             +++ (symbol "&&" >> return TAnd)
             +++ (symbol "||" >> return TOr)

parseApp :: [String] -> Parser TypedTerm
parseApp ctx = do
  terms <- many1 (parseAtom ctx)
  return $ foldl1 TApp terms

parseAtom :: [String] -> Parser TypedTerm
parseAtom ctx =
      parseList ctx
  +++ parseBool
  +++ parseInt
  +++ parseVar ctx
  +++ parseParens ctx

parseLam :: [String] -> Parser TypedTerm
parseLam ctx = do
  symbol "\\"
  x <- ident
  symbol ":"
  ty <- parseType
  symbol "."
  body <- parseExpr (x:ctx)
  return $ TLam x ty body

parseVar :: [String] -> Parser TypedTerm
parseVar ctx = do
  x <- ident
  return (TVar x)

parseInt :: Parser TypedTerm
parseInt = TIntLit . read <$> (skipSpaces *> munch1 isDigit)

parseBool :: Parser TypedTerm
parseBool =
      (symbol "True" >> return (TBoolLit True))
  +++ (symbol "False" >> return (TBoolLit False))

parseList :: [String] -> Parser TypedTerm
parseList ctx =
      parseNil
  +++ parseCons ctx

parseNil :: Parser TypedTerm
parseNil = symbol "[]" >> return (TNil TInt) 

parseCons :: [String] -> Parser TypedTerm
parseCons ctx = do
  symbol "["
  elems <- sepBy (parseExpr ctx) (symbol ",")
  symbol "]"
  return $ foldr TCons (TNil TInt) elems 

parseParens :: [String] -> Parser TypedTerm
parseParens ctx = between (symbol "(") (symbol ")") (parseExpr ctx)

parseFull :: String -> Either String TypedTerm
parseFull s = case readP_to_S (parseExpr [] <* skipSpaces <* eof) s of
  [(res, _)] -> Right res
  _          -> Left "Parse error: Ne mogu parsirati izraz."

-- === Env Replace ===

substituteEnv :: Env -> TypedTerm -> TypedTerm
substituteEnv env (TVar x) = case lookup x env of
  Just t  -> substituteEnv env t
  Nothing -> TVar x
substituteEnv env (TLam x ty t) = TLam x ty (substituteEnv env t)
substituteEnv env (TApp a b) = TApp (substituteEnv env a) (substituteEnv env b)
substituteEnv env (TIntLit n) = TIntLit n
substituteEnv env (TAdd a b) = TAdd (substituteEnv env a) (substituteEnv env b)
substituteEnv env (TMul a b) = TMul (substituteEnv env a) (substituteEnv env b)
substituteEnv env (TBoolLit b) = TBoolLit b
substituteEnv env (TAnd a b) = TAnd (substituteEnv env a) (substituteEnv env b)
substituteEnv env (TOr a b) = TOr (substituteEnv env a) (substituteEnv env b)
substituteEnv env (TNot a) = TNot (substituteEnv env a)
substituteEnv env (TNil ty) = TNil ty
substituteEnv env (TCons h t) = TCons (substituteEnv env h) (substituteEnv env t)

-- === Pretty Print ===

prettyPrint :: Term -> String
prettyPrint (Var x) = "Var " ++ show x
prettyPrint (Lam t) = "(\\" ++ prettyPrint t ++ ")"
prettyPrint (App t u) = "(" ++ prettyPrint t ++ " " ++ prettyPrint u ++ ")"
prettyPrint (IntLit n) = show n
prettyPrint (Add t u) = "(" ++ prettyPrint t ++ " + " ++ prettyPrint u ++ ")"
prettyPrint (Mul t u) = "(" ++ prettyPrint t ++ " * " ++ prettyPrint u ++ ")"
prettyPrint (BoolLit b) = if b then "True" else "False"
prettyPrint (And t u) = "(" ++ prettyPrint t ++ " && " ++ prettyPrint u ++ ")"
prettyPrint (Or t u) = "(" ++ prettyPrint t ++ " || " ++ prettyPrint u ++ ")"
prettyPrint (Not t) = "(!" ++ prettyPrint t ++ ")"
prettyPrint Nil = "[]"
prettyPrint (Cons h t) = "[" ++ elems (Cons h t) ++ "]"
  where
    elems Nil = ""
    elems (Cons x xs) = prettyPrint x ++ rest xs
    rest Nil = ""
    rest (Cons x xs) = ", " ++ prettyPrint x ++ rest xs
    rest _ = error "Malformed list"

-- === REPL ===

main :: IO ()
main = do
  putStrLn "Type :q to quit."
  repl []

repl :: Env -> IO ()
repl env = do
  putStr ">>> "
  hFlush stdout
  input <- getLine
  if input == ":q"
    then putStrLn "Bye!"
    else case words input of
      (name:":=":rest) -> case parseFull (unwords rest) of
        Left err -> putStrLn err >> repl env
        Right t  -> putStrLn ("Defined " ++ name) >> repl ((name, t):env)
      _ -> case parseFull input of
        Left err -> putStrLn err >> repl env
        Right t -> do
          let t' = substituteEnv env t
              ctx = [(n, ty) | (n, tdef) <- env, Just ty <- [infer [] tdef]]
          case infer ctx t' of
            Nothing -> putStrLn "Type error." >> repl env
            Just _  -> putStrLn (prettyPrint (eval (erase t'))) >> repl env