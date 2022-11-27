{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module MiniLambda where
import Data.Map (Map, empty, (!), insert, union, toList)
import Effectful
import Data.List ((++), sort)
import Data.Char
import Text.Parsec
import Data.Vector hiding ((++))
import Control.Monad.IO.Class
import Data.Hashable
import GHC.Generics (Generic)

data MiniLambda = 
    App MiniLambda MiniLambda
    |Abs String MiniLambda
    |Var String
    |Pi String MiniLambda MiniLambda deriving (Eq, Generic, Hashable)

instance Show MiniLambda where
    show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"
    show (Abs name y) = "λ" ++ name ++ "." ++ (show y)
    show (Var x) = x
    show (Pi name type' body) = "Π" ++ " (" ++ name ++ ":" ++ show type' ++ ")." ++ show body

type TreeType = MiniLambda
type Term = (TreeType, TreeType)
type Clause = (String, TreeType)
data SearchAST = SearchAST TreeType (Vector Clause) deriving Show

data Progress = Depedency Int | Free Term deriving Show
data Problem = Problem SearchAST Progress deriving Show

type Rules = TreeType -> Maybe Problem

type SetProblems = Map Int Problem
newtype Nodes = Nodes (SetProblems) deriving Show

substitute :: (String, MiniLambda) -> MiniLambda -> MiniLambda
substitute params (App func body) = App (substitute params func) (substitute params body)
substitute params (Abs name body) = Abs name $ substitute params body
substitute params (Pi name type_ body) = Pi name (substitute params type_) (substitute params body)
substitute (origin, term) v@(Var target) = if origin == target then term else v

consumeRef :: Parsec String st String
consumeRef = many1 alphaNum

consumePiType :: Parsec String st TreeType
consumePiType = do
    string ("[")
    string "("
    param <- consumeRef
    spaces
    string ":"
    spaces
    type_ <- consumeMiniLambda
    spaces
    string ")"
    spaces
    string "->"
    spaces
    body <- consumeMiniLambda
    string ("]")
    return (Pi param type_ body)

parseTypeNotation :: Parsec String st TreeType
parseTypeNotation = try (consumePiType) <|> consumeMiniLambda

consumeVar :: Parsec String st MiniLambda
consumeVar = do
    var <- consumeRef
    return (Var var)

consumeAbs :: Parsec String st MiniLambda
consumeAbs = do
    string "\\"
    ref <- consumeRef
    spaces
    string "=>"
    spaces
    body <- consumeMiniLambda
    return (Abs ref body)

consumeApp :: Parsec String st MiniLambda
consumeApp = do
    string "("
    x <- consumeMiniLambda
    many1 space
    y <- consumeMiniLambda
    string ")"
    return (App x y)

consumeMiniLambda :: Parsec String st MiniLambda
consumeMiniLambda = choice [consumeApp, consumePiType, consumeAbs, consumeVar]

parseDeclarations :: Parsec String st (String, TreeType)
parseDeclarations = do
    name <- consumeRef
    spaces
    string "="
    spaces
    lamdba_expr <- parseTypeNotation
    return (name, lamdba_expr)

parseBlock :: Parsec String st SearchAST
parseBlock = do
    x <- many parseStatement
    string ":"
    spaces
    goal_term <- parseTypeNotation
    return (SearchAST goal_term (Data.Vector.fromList x))
  where 
    parseStatement = do
        decl <- parseDeclarations
        many1 (char '\n')
        return decl


type USearch a = Nodes -> Map String Rules -> IO (a, Nodes, Map String Rules)

newtype Search a = Wrap (USearch a)

instance Functor Search where
  fmap f (Wrap serch_a) = Wrap (\nodes rules -> do
     (a, nodes', rules') <- serch_a nodes rules
     return (f a, nodes', rules'))

unique :: a -> USearch a
unique k nodes rules = return (k, nodes, rules)

instance Applicative Search where
  pure a = Wrap (unique a)
  (<*>) (Wrap fab) (Wrap search_a) = Wrap (\nodes rules -> do
    (a, nodes', rules') <- search_a nodes rules
    (ab, nodes'', rules'') <- fab nodes' rules'
    return (ab a, nodes'', rules''))

bind  :: forall a b. USearch a -> (a -> USearch b) -> USearch b
bind k f nodes rules = do
   (a, nodes', rules') <- k nodes rules
   f a nodes' (Data.Map.union rules rules')

instance Monad Search where
  (>>=) (Wrap search_a) f = Wrap (bind search_a (\a -> do
    let (Wrap search) = f a
    search
   ))

instance MonadIO Search where
    liftIO io = Wrap (\nodes map -> io >>= return . (, nodes, map))

saveNode :: (Int, Problem) -> Search ()
saveNode (k, x) = Wrap (\nodes@(Nodes map) rules -> return ((), Nodes (Data.Map.insert k x map), rules))

pushNode :: Problem -> Search ()
pushNode problem = do
    hash <- generateHashContext problem
    saveNode (hash, problem)

getNodes :: Search Nodes
getNodes = Wrap (\nodes@(Nodes map) rules -> return (nodes, nodes, rules))

getProblems :: Search [Problem]
getProblems = do
    (Nodes nodes) <- getNodes
    return $ fmap snd $ Data.Map.toList nodes

getClauses :: Search Nodes
getClauses = Wrap (\nodes@(Nodes map) rules -> return (nodes, nodes, rules))

generateHashContext :: Problem -> Search Int
generateHashContext (Problem (SearchAST goal clauses) (Free (term, tree))) = do
    let hash_clauses = Data.Vector.map (hash . snd) clauses
    let sorted_hashes = Data.List.sort (Data.Vector.toList hash_clauses)
    nodes <- getNodes
    return $ hash (hash tree : sorted_hashes)
   where
       hash_depencies (Free (term, tree)) nodes = return $ hash tree
       hash_depencies (Depedency hash) nodes = do
        let problem = (nodes Data.Map.! hash)
        generateHashContext problem

selectOnePertubation :: Vector a -> Search (Maybe a)
selectOnePertubation as
    |Data.Vector.null as = return Nothing
    |otherwise = do
        r <- liftIO $ randIO (0, (Data.Vector.length $ as) - 1)
        return $ Just $ as Data.Vector.! r

filterByType :: TreeType -> TreeType -> Bool 
filterByType v@(Var _) v'@(Var _) = v == v'
filterByType v (Pi _ type_ _) = v == type_
filterByType _ _ = False

selectCompatibleTypeClauses :: TreeType -> SearchAST -> (Vector Clause) 
selectCompatibleTypeClauses term (SearchAST _ vec) = Data.Vector.filter (filterByType term . snd) vec

selectClauseByEmptyState :: Clause -> SearchAST -> Search Problem
selectClauseByEmptyState (name_term, type_) ast = do
    return (Problem ast (Free (Var name_term, type_)))

piReduction :: (Term, Term) -> Term
piReduction ((expr, type_), (function, Pi name param body)) = ((App function expr), substitute (name, body) expr)

doAction :: Clause -> Term -> Search Term 
doAction (name, pi@(Pi _ _ _)) term = return $ piReduction (term, (Var name, pi))  

exploreProblem :: Problem -> Search (Maybe Problem)
exploreProblem (Problem ast (Free (expr, type_))) = do
    clause <- selectOnePertubation . selectCompatibleTypeClauses type_ $ ast
    case clause of {
        Just clause -> (do
            term <- doAction clause (expr, type_)
            return (Just (Problem ast (Free term))));
        Nothing -> (return Nothing);
    }

expandByAction :: SearchAST -> Search ()
expandByAction s@(SearchAST goal decls)  = do
    clause <- selectOnePertubation decls
    case clause of {
        Just clause -> (do
            problem <- selectClauseByEmptyState clause s
            pushNode problem
        );
        Nothing -> (do
            return ()
        );
    }

iterateSolutions :: [Problem] -> Search ()
iterateSolutions [] = return ()
iterateSolutions (p@(Problem _ _) : ps) = do
    problem <- exploreProblem p
    case problem of {
        Just x -> pushNode x;
        Nothing -> return ();
    }
    return ()

searchSolution :: SearchAST -> Search ()
searchSolution ast = do
    expandByAction ast
    problems <- getProblems
    iterateSolutions problems

readMiniLambda :: String -> Either ParseError (IO Nodes)
readMiniLambda str = do
    case (parse parseBlock "" str) of {
        Left x -> Left x;
        Right ast -> return $ do
            let (Wrap r) = searchSolution ast
            (a, nodes, map) <- r (Nodes Data.Map.empty) Data.Map.empty
            return nodes
    }