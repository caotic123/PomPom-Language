{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
module MiniLambda where
import Data.Map (Map, empty, (!), insert, union, toList, lookup, member)
import Effectful
import Util
import Control.Monad
import Data.Maybe
import Data.List ((++), sort)
import Data.Char
import Text.Parsec
import Data.Vector hiding ((++))
import Control.Monad.IO.Class
import Data.Hashable
import GHC.Generics (Generic)

data VarRef = Name String | Paralell Int deriving (Eq, Generic, Hashable)

data MiniLambda = 
    App MiniLambda MiniLambda
    |Abs String MiniLambda
    |Var VarRef
    |Pi String MiniLambda MiniLambda deriving (Eq, Generic, Hashable)

instance Show MiniLambda where
    show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"
    show (Abs name y) = "λ" ++ name ++ "." ++ (show y)
    show (Var (Name x)) = x
    show (Var (Paralell x)) = "[" ++ (show x) ++ "]"
    show (Pi name type' body) = "Π" ++ " (" ++ name ++ ":" ++ show type' ++ ")." ++ show body

type TreeType = MiniLambda
type Term = (TreeType, TreeType)
type Clause = (String, TreeType)
data SearchAST = SearchAST TreeType (Vector Clause) deriving Show

data Problem = Problem SearchAST (Maybe Term)

instance Show Problem where
    show (Problem (SearchAST goal _) (Just (term, type_))) = show term ++ " : " ++ show type_ ++ " goal : " ++ show goal ++ "\n"
    show (Problem (SearchAST goal _) Nothing) = " ? " ++  "goal : " ++ show goal ++ "\n"

type Rules = TreeType -> Maybe Problem

type SetProblems = Map Int Problem
type SetTypes = Map Int Int
data Nodes = Nodes (SetProblems) (SetTypes) deriving Show

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
    return (Var (Name var))

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
bind k f (Nodes nodes types) rules = do
   (a, (Nodes nodes' types'), rules') <- k (Nodes nodes types) rules
   f a (Nodes (Data.Map.union nodes' nodes) (Data.Map.union types' types)) (Data.Map.union rules' rules)

instance Monad Search where
  (>>=) (Wrap search_a) f = Wrap (bind search_a (\a -> do
    let (Wrap search) = f a
    search
   ))

instance MonadIO Search where
    liftIO io = Wrap (\nodes map -> io >>= return . (, nodes, map))

saveNode :: (Int, Problem) -> Search ()
saveNode (k, x) = Wrap (\nodes@(Nodes map types) rules -> return ((), Nodes (Data.Map.insert k x map) types, rules))

saveTypePath :: (Int, Int) -> Search ()
saveTypePath (k, x) = Wrap (\nodes@(Nodes map types) rules -> return ((), Nodes map (Data.Map.insert k x types), rules))

getNode :: Int -> Search Problem
getNode k = Wrap (\nodes@(Nodes map types) rules -> return (map Data.Map.! k, nodes, rules))

checkNode :: Int -> Search Bool
checkNode k = Wrap (\nodes@(Nodes map types) rules -> return (member k map, nodes, rules))

getGoal :: Problem -> TreeType
getGoal (Problem (SearchAST goal _) _) = goal

get_safe_node :: Int -> Search (Maybe Problem)
get_safe_node k = Wrap (\nodes@(Nodes map types) rules -> return (Data.Map.lookup k map, nodes, rules))

createProblem :: TreeType -> Vector Clause -> Search Int
createProblem goal clauses = do
    let ast = SearchAST goal clauses
    startNode ast

pushNode :: Problem -> Search Int
pushNode problem@(Problem ast term) = do
    let key = generateHashContext ast
    -- let hash_node = hash $ getGoal problem
    check <- checkNode key
    if check then
        return key
    else do
        saveNode (key, problem)
        -- saveTypePath (hash_node, key)
        return key

updateNode :: Int -> Problem -> Search Int
updateNode key problem = do
    n <- liftIO $ randIO (0, 999999)
    saveNode (key, problem)
    return n

mapNode :: Int -> (Problem -> Problem) -> Search ()
mapNode key f = do
    node <- getNode key
    void $ updateNode key (f node)

getTerm :: Problem -> Maybe Term
getTerm (Problem ast term) = term

extendContext :: (String, TreeType) -> Problem -> Problem
extendContext (name, type') (Problem (SearchAST goal context) term) = 
    Problem (SearchAST goal (cons (name, type') context)) term

setTerm :: Int -> Term -> Search ()
setTerm k term = do
    (Problem ast term') <- getNode k
    saveNode (k, Problem ast (Just term))

getNodes :: Search Nodes
getNodes = Wrap (\nodes@(Nodes map types) rules -> return (nodes, nodes, rules))

getProblems :: Search [(Int, Problem)]
getProblems = do
    (Nodes nodes types) <- getNodes
    return $ Data.Map.toList nodes

generateHashContext :: SearchAST -> Int
generateHashContext (SearchAST goal clauses) = do
    let hash_clauses = Data.Vector.map (hash . snd) clauses
    let sorted_hashes = Data.List.sort (Data.Vector.toList hash_clauses)
    hash (hash goal : sorted_hashes)

selectOnePertubation :: Vector a -> Search (Maybe a)
selectOnePertubation as
    |Data.Vector.null as = return Nothing
    |otherwise = do
        r <- liftIO $ randIO (0, (Data.Vector.length $ as) - 1)
        return $ Just $ as Data.Vector.! r

isReductible :: TreeType -> TreeType -> Bool 
isReductible v (Pi _ type_ _) = v == type_
isReductible _ _ = False

searchPiReductible :: TreeType -> SearchAST -> (Vector Clause) 
searchPiReductible term (SearchAST _ vec) = Data.Vector.filter (isReductible term . snd) vec

filterHeadByType :: TreeType -> TreeType -> Bool 
filterHeadByType v@(Var _) v'@(Var _) = v == v'
filterHeadByType v (Pi _ type_ _) = v == type_
filterHeadByType t t' = t == t'

isEqualTailPi :: TreeType -> TreeType -> Bool 
isEqualTailPi final_type pi'@(Pi _ _ _) = final_type == getPiFinalType pi'
isEqualTailPi t t' = filterHeadByType t t'

selectReachablePi :: TreeType -> Vector (a, TreeType) -> Vector (a, TreeType)
selectReachablePi term vec = Data.Vector.filter (isEqualTailPi term . snd) vec

piToList :: MiniLambda -> [MiniLambda]
piToList pi = go pi []
  where 
    go pi@(Pi name _ body) ls = go body (pi : ls)
    go _ ls = ls
    
-- selectDerivableFuncs :: TreeType -> SearchAST -> (Vector Clause) 
selectDerivableFuncs :: MiniLambda -> Vector (a, MiniLambda) -> [((a, MiniLambda), [(Maybe MiniLambda, MiniLambda)])]
selectDerivableFuncs param vec = do
    Data.Vector.foldl selectPiTypes [] vec
    where
        selectPiTypes ls all@(_, pi@(Pi name _ body)) = do
            let param_equality = Prelude.map (\target -> (if filterHeadByType param target then Just param else Nothing, target)) (piToList pi)
            if Prelude.any (isJust . fst) param_equality
                then (all, param_equality) : ls
            else ls
        selectPiTypes ls _ = ls

betaExpand :: SearchAST -> Search Problem
betaExpand ast@(SearchAST pi@(Pi name pi_type body) clauses) = do
    node_id <- createProblem body clauses
    mapNode node_id (extendContext (name, pi_type))
    return (Problem ast (Just (Abs name (Var $ Paralell node_id), pi)))

selectClauseByEmptyState :: Clause -> SearchAST -> Search Problem
selectClauseByEmptyState (name_term, type_@(Pi _ _ _)) ast@(SearchAST goal clauses) = do
    -- term <- constructPartialApplication type_
    return (Problem ast (Just (Var $ Name name_term, type_)))
  where
    constructPartialApplication (Pi _ type_ body) = do
        rec_ <- constructPartialApplication body
        node_id <- createProblem type_ clauses
        return $ App rec_ (Var $ Paralell node_id)
    constructPartialApplication _ = return $ Var (Name name_term)

selectClauseByEmptyState (name_term, type_) ast@(SearchAST goal clauses) = do
    return (Problem ast (Just (Var (Name name_term), type_)))

substitute :: (MiniLambda, MiniLambda) -> MiniLambda -> Search MiniLambda
substitute params (App func body) = do
    func <- (substitute params func) 
    body <- (substitute params body)
    return $ App func body
substitute params (Abs name body) = do
    body <- substitute params body
    return $ Abs name $ body
substitute params (Pi name type_ body) = do
    type_ <- (substitute params type_)
    body <- (substitute params body)
    return $ Pi name type_ body
substitute (origin, term) v@(Var (Paralell target)) = do
    type_ <- getTerm <$> (getNode target)
    case type_ of {
        Just (term, type_) -> (do
            map <- (substitute (origin, term) term)
            setTerm target (map, type_)
            return v   
        );
        Nothing -> return v;
    }
substitute (origin, term) v = return $ if origin == v then term else v

getPiFinalType :: TreeType -> TreeType
getPiFinalType (Pi _ _ body) = getPiFinalType body
getPiFinalType v = v

getPiHeadType :: TreeType -> TreeType
getPiHeadType (Pi _ type_ body) = type_
getPiHeadType _ = error "Not a pi type applied on getPiHeadType"

piReduction :: (Term, Term) -> Search Term
piReduction ((expr, type_), (function, Pi name param body)) = do
    subs <- substitute (Var $ Name name, body) expr
    return ((App function expr), subs)

piHeadReduction :: Problem -> Search (Maybe Problem)
piHeadReduction (Problem ast (Just (expr, type_))) = do
    clause <- selectOnePertubation . searchPiReductible type_ $ ast
    liftIO $ print clause
    case clause of {
        Just clause -> (do
            term <- doAction clause (expr, type_)
            return (Just (Problem ast (Just term))));
        Nothing -> (return Nothing);
    }
  where
    doAction :: Clause -> Term -> Search Term 
    doAction (name, pi@(Pi _ _ _)) term = piReduction (term, (Var (Name name), pi))  

expandPiReduction :: Problem -> Search (Maybe Problem)
expandPiReduction  (Problem ast@(SearchAST goal clauses) (Just (expr, type_))) = do
    let clausesCompatible = selectReachablePi goal clauses
    liftIO $ print (goal, clausesCompatible)
    clause <- selectOnePertubation . fromList . selectDerivableFuncs type_ $ clausesCompatible
    case clause of {
        Just (clause, piConstruction) -> (do
            -- let ((name, term), param_pos) = (fst clause, fromJust . snd $ clause)
            (regex, term) <- constructParallelFunc piConstruction (Var $ Name $ fst clause)
            type' <- case regex of {
                Just regex -> substitute (regex, expr) $ getPiFinalType $ snd clause;
                Nothing -> return $ getPiFinalType $ snd clause;
            }
            return . Just $ Problem ast (Just (term, type'))
        );
        Nothing -> return Nothing;
    }
  where
    constructParallelFunc (pi : pi' : xs) base_case = do
        (regex', rec_) <- constructParallelFunc (pi' : xs) base_case
        (regex, param) <- constructParam pi
        return (Util.or regex regex', (App param rec_))
    constructParallelFunc (pi : []) base_case = do
        (regex, param) <- constructParam pi 
        return (regex, App base_case param)
    constructParam (Just complete_param, _) = return (Just complete_param, expr)
    constructParam (Nothing, type_) = do
        node_id <- createProblem (getPiHeadType type_) clauses
        return $ (Nothing, Var $ Paralell node_id)

tryFirstTerm :: Problem -> Search Problem
tryFirstTerm (Problem ast@(SearchAST goal clauses) _) = do
    clause <- selectOnePertubation clauses
    -- clause <- selectOnePertubation clauses
    case clause of {
        Just clause -> selectClauseByEmptyState clause ast;
        Nothing -> return $ Problem ast Nothing
    }

exploreProblem :: Problem -> Search (Maybe Problem)
exploreProblem problem@(Problem ast@(SearchAST pi@(Pi _ _ _) _) Nothing) = do
    Just <$> (betaExpand ast)
exploreProblem problem@(Problem ast Nothing) = do
    Just <$> (tryFirstTerm problem)
exploreProblem problem@(Problem ast (Just _)) = do
    -- n <- liftIO $ randIO (1, 100)
    piHeadReduction problem

startNode :: SearchAST -> Search Int
startNode ast@(SearchAST goal decls) = pushNode $ Problem ast Nothing

checkIfReachGoal :: Problem -> Bool
checkIfReachGoal (Problem (SearchAST goal _) (Just (_, type'))) = goal == type'
checkIfReachGoal _ = False

iterateSolutions :: [(Int, Problem)] -> Search ()
iterateSolutions [] = return ()
iterateSolutions ((key, p@(Problem _ _)) : ps) = do
    if checkIfReachGoal p then
        return ()
    else do
        problem <- exploreProblem p
        case problem of {
            Just x -> void $ updateNode key x;
            Nothing -> return ();
         }
        iterateSolutions ps

search :: Search ()
search = getProblems >>= iterateSolutions

iterateSearch :: Int -> Search ()
iterateSearch 0 = return ()
iterateSearch n = do
    search
    iterateSearch (n - 1)

searchSolution :: SearchAST -> Search ()
searchSolution ast = do
    startNode ast
    iterateSearch 20

readMiniLambda :: String -> Either ParseError (IO Nodes)
readMiniLambda str = do
    case (parse parseBlock "" str) of {
        Left x -> Left x;
        Right ast -> return $ do
            let (Wrap r) = searchSolution ast
            (a, nodes, map) <- r (Nodes Data.Map.empty Data.Map.empty) Data.Map.empty
            return nodes
    }
