{-# LANGUAGE TupleSections #-}
module Parser where

import Prelude
import Text.Parsec
import Data.Char ( isAlphaNum, isSpace )
import Data.Functor
import Control.Monad

type PDefinitons = (String, PTerm)
type PDataTypes = (String, PTerm)
data PTerm =
    PSelf String String PTerm PTerm
  | PLam [String] PTerm PTerm
  | PApp PTerm PTerm
  | PVar String
  | PMatch PTerm PTerm [(PTerm, PTerm)]
  | PTatic [PTerm] deriving Show


varCharacters :: [Char]
varCharacters = ['_', '\'', '≡', 'σ', '+', '*', '⊥', '△', '>', '<', 'Ǝ', '=', '!', '?']

consumeVarName :: Parsec String st String
consumeVarName = many1 $ satisfy (\x -> not (isSpace x) && (isAlphaNum x || elem x varCharacters))

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

consumeArgs :: Parsec String st (String, String, PTerm)
consumeArgs = consumeFreeType <|> consumeSelfType
  where
    consumeFreeType = do
        withSpaces . string $ "~"
        x <- withSpaces parseTerm
        return ("", "", x)
    consumeSelfType = do
        self <- try consumeVarName <|> return ""
        justParent $ do
          x <- consumeVarName
          withSpaces . string $ ":"
          t <- withSpaces parseTerm
          return (self, x, t)

parseSelf :: Parsec String st PTerm
parseSelf = do
    (self, x, t) <- consumeArgs
    withSpaces (string "->")
    l <- withSpaces parseTerm
    return (PSelf self x t l)
  where
    consumeFreeType = do
        withSpaces . string $ "~"
        x <- withSpaces parseTerm
        return ("", "", x)
    consumeSelfType = do
        self <- try consumeVarName <|> return ""
        justParent $ do
          x <- consumeVarName
          withSpaces . string $ ":"
          t <- withSpaces parseTerm
          return (self, x, t)

parseLambda :: Parsec String st PTerm
parseLambda = do
    withSpaces . string $ "|"
    args <- many1 $ withSpaces consumeVarName
    withSpaces . string $ "::"
    type_ <- withSpaces parseSelf
    withSpaces . string $ "=>"
    body <- parseTerm
    return $ PLam args body type_
    
parseApp :: Parsec String st PTerm
parseApp = justParent app
  where
    app = do
        x <- parseTerm
        y <- many1 (space >> parseTerm)
        return (Prelude.foldl PApp x y)

parseTactics :: Parsec String st PTerm
parseTactics = do
    between (string "{") (string  "}") terms <&> PTatic
  where
      terms = many1 (withSpaces parseTerm >>= (\a -> (withSpaces . string $ ";") >> return a))

parseTerm :: Parsec String st PTerm
parseTerm =
    optional_parent (choice [try parseLambda, try parseSelf, try parseApp, try parseTactics, try parseMatching, parseVar])
  where
      optional_parent term = try term <|> justParent term

parseMatching :: Parsec String st PTerm
parseMatching = matching
 where
    matching = do
        withSpaces . char $ '['
        k <- parseTerm
        many1 space
        string "of"
        many1 space
        type' <- withSpaces parseTerm
        withSpaces $ return ()
        x <- many matchs
        withSpaces . char $ ']'
        return (PMatch k type' x)
    matchs = do
        withSpaces . string $ "|"
        k <- parseTerm
        withSpaces . string $ "=>"
        y' <- withSpaces parseTerm
        return (k, y')
    parseFreeVars = do
        many (try (consumeVarName >>= (\a -> space >> return (PVar a))) <|> (consumeVarName <&> PVar))

parseDefinition :: Parsec String st [PDefinitons]
parseDefinition = many1 $ do
    def_name <- consumeVarName
    term <- withSpaces parseTerm
    withSpaces . string $ "."
    return (def_name, term)

parseData :: Parsec String st PDataTypes
parseData = do
    def_name <- consumeVarName
    term <- withSpaces parseTerm
    withSpaces . string $ "."
    return (def_name, term)

run :: String -> Either ParseError [PDefinitons]
run = parse parseDefinition ""