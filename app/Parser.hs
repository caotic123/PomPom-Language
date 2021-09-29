{-# LANGUAGE TupleSections #-}
module Parser where

import Prelude
import Text.Parsec
import Data.Char ( isAlphaNum, isSpace )
import Data.Functor
import Control.Monad

data Sort = SortStatement | SortStatic deriving Show
type PDefinitons = (String, Sort, PTerm)

type PDataTypes = (String, PTerm)
data PTerm =
    PType String PTerm PTerm
  | PLam [String] PTerm (Maybe PTerm)
  | PApp PTerm PTerm
  | PVar String
  | PMatch PTerm PTerm [(PTerm, PTerm)]
  | PConstructors PTerm [PTerm]
  | PTatic [PTerm]
  | PNotation PTerm PTerm
  | PDef String PTerm PTerm
  deriving Show

varCharacters :: [Char]
varCharacters = [':', '(', ')', '.', '|', '~', '>', '{', '}', '=', '[', ']', ';']

consumeVarName :: Parsec String st String
consumeVarName = many1 $ satisfy (\x -> not (isSpace x) && (isAlphaNum x || notElem x varCharacters))

withSpaces :: Parsec String st a -> Parsec String st a
withSpaces k = char_ignorable >> k >>= (\a -> char_ignorable >> return a)
 where
    char_ignorable = do
        let tryC a b = (a <|> b) <|> (b <|> a)
        tryC spaces (void (try $ many (char '\n')))

justParent :: Parsec String st a -> Parsec String st a
justParent k = between (char '(') (char ')') (withSpaces k)

parseVar :: Parsec String st PTerm
parseVar = consumeVarName <&> PVar

consumeArgs :: Parsec String st (String, PTerm)
consumeArgs = consumeFreeType <|> consumeSelfType
  where
    consumeFreeType = do
        withSpaces . string $ "~"
        x <- withSpaces parseTerm
        return ("", x)
    consumeSelfType = justParent $ do
          x <- consumeVarName
          withSpaces . string $ ":"
          t <- withSpaces parseTerm
          return (x, t)

parseConstructors :: Parsec String st PTerm
parseConstructors = do
     between (char '{') (char '}') constructors
  where
      constructors = do
          type_ <- parseTerm
          withSpaces . string $ "::"
          patterns <- many $ withSpaces ((withSpaces . string $ "|") >> parseTerm)
          return (PConstructors type_ patterns)

parseType :: Parsec String st PTerm
parseType = do
    (x, t) <- consumeArgs
    try (withSpaces $ void (string "~>")) <|> (space >> withSpaces (return ()))
    l <- withSpaces parseTerm
    return (PType x t l)

parseUnTypedLambda :: Parsec String st PTerm
parseUnTypedLambda = do
    withSpaces . string $ "|"
    args <- many1 $ withSpaces consumeVarName
    withSpaces . string $ "=>"
    body <- withSpaces parseTerm
    return $ PLam args body Nothing 

parseLambda :: Parsec String st PTerm
parseLambda = do
    withSpaces . string $ "|"
    args <- many1 $ withSpaces consumeVarName
    type_ <- parseLambdaType
    withSpaces . string $ "=>"
    body <- parseTerm
    return $ PLam args body type_
  where
    parseLambdaType = do    
      withSpaces . string $ "::"
      term <- withSpaces parseTerm
      return $ Just term

parseApp :: Parsec String st PTerm
parseApp = justParent app
  where
    app = do
        x <- parseTerm
        y <- many1 (space >> parseTerm)
        return (Prelude.foldl PApp x y)

parseTypeNotation :: Parsec String st PTerm
parseTypeNotation = between (char '(') (char ')') notation
  where
  notation = do
      term <- withSpaces parseTerm
      withSpaces $ string "::"
      type_ <- withSpaces parseTerm
      return (PNotation term type_)

parseDef :: Parsec String st PTerm
parseDef = do
    withSpaces . string $ "def"
    def_name <- consumeVarName
    withSpaces . string $ "="
    term_head <- parseTerm
    withSpaces . string $ ";"
    PDef def_name term_head <$> parseTerm

parseTactics :: Parsec String st PTerm
parseTactics = do
    between (string "{") (string  "}") terms <&> PTatic
  where
      terms = many1 (withSpaces parseTerm >>= (\a -> (withSpaces . string $ ";") >> return a))

parseStatic :: Parsec String st PDefinitons
parseStatic = do
    withSpaces . string $ "Static"
    name <- withSpaces consumeVarName
    withSpaces . string $ ":"
    term <- parseTerm
    withSpaces . string $ "."
    return (name, SortStatic, term)

parseTerm :: Parsec String st PTerm
parseTerm =
    optional_parent (choice [try parseUnTypedLambda, try parseLambda, try parseType, try parseConstructors, try parseApp, try parseTactics, try parseDef, try parseTypeNotation, try parseMatching, parseVar])
  where
      optional_parent term = try term <|> justParent term

parseMatching :: Parsec String st PTerm
parseMatching = matching
 where
    matching = do
        withSpaces $ char '['
        k <- parseTerm
        withSpaces $ string "of"
        type' <- withSpaces parseTerm
        withSpaces $ return ()
        x <- withSpaces $ many matchs
        withSpaces $ char ']'
        return (PMatch k type' x)
    matchs = do
        withSpaces . string $ "|"
        k <- parseTerm
        withSpaces . string $ "=>"
        y' <- withSpaces parseTerm
        return (k, y')
    parseFreeVars = do
        many (try (consumeVarName >>= (\a -> withSpaces space >> return (PVar a))) <|> (consumeVarName <&> PVar))

parseStatements :: Parsec String st PDefinitons
parseStatements = do
    def_name <- consumeVarName
    term <- withSpaces parseTerm
    withSpaces . string $ "."
    return (def_name, SortStatement, term)

parseDefinition :: Parsec String st [PDefinitons]
parseDefinition = many $ try parseStatic <|> parseStatements

run :: String -> Either ParseError [PDefinitons]
run = parse parseDefinition ""