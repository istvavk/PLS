import Text.ParserCombinators.ReadP
import Data.Char

-- === Tipovi ===
data Type = T String | Arrow Type Type
  deriving (Show, Eq)

type Parser a = ReadP a

symbol :: String -> Parser String
symbol s = skipSpaces *> string s <* skipSpaces

ident :: Parser String
ident = skipSpaces *> munch1 isAlpha <* skipSpaces

parseType :: Parser Type
parseType = chainr1 parseAtomicType (symbol "->" >> return Arrow)

parseAtomicType :: Parser Type
parseAtomicType =
      (T <$> ident)
  +++ between (symbol "(") (symbol ")") parseType

parseTypeWithSpaces :: Parser Type
parseTypeWithSpaces = skipSpaces *> parseType <* skipSpaces

-- === Lambda izrazi sa tipovima ===
data TypedTerm = TVar Int | TLam TypedTerm Type | TApp TypedTerm TypedTerm
  deriving (Show, Eq)

parseTypedTerm :: [String] -> Parser TypedTerm
parseTypedTerm ctx = parseLam ctx +++ parseApp ctx

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

parseApp :: [String] -> Parser TypedTerm
parseApp ctx = chainl1 (parseAtom ctx) (return TApp)

parseAtom :: [String] -> Parser TypedTerm
parseAtom ctx = parseVar ctx +++ between (symbol "(") (symbol ")") (parseTypedTerm ctx)

-- === Helper za testiranje ===
parseFull :: String -> Either String TypedTerm
parseFull input = case readP_to_S (parseTypedTerm [] <* skipSpaces <* eof) input of
  [(res, "")] -> Right res
  _ -> Left "Ne mogu parsirati izraz."

-- === Main za testiranje ===
main :: IO ()
main = do
  let testCases =
        [ "\\x:A. x"
        , "\\x:A. \\y:A. x"
        , "\\x:(A->A). x"
        , "\\x:A. \\f:(A->A). f x"
        , "(\\x:A. x) (\\y:A. y)"
        ]
  mapM_ testParse testCases

testParse :: String -> IO ()
testParse s = do
  putStrLn $ "Input: " ++ s
  case parseFull s of
    Left err -> putStrLn $ "Error: " ++ err
    Right t -> putStrLn $ "Parsed: " ++ show t
  putStrLn ""

