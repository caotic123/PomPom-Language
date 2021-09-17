
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Term where
import Debug.Trace
import Util

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric (showHex)
import Data.Bifunctor
import Data.Sequence

import Parser
import Effectful

data VarName = VarName Int | VarRef String deriving (Eq, Ord)

instance Show VarName where
  show (VarName i) = showHex i ""
  show (VarRef i) = i

varEmpty :: VarName
varEmpty = VarName 0

data Term =
   Pi Term Term Term
  | Lam Term Term
  | App Term Term
  | Var VarName
  | Constr Term [Term]
  | Match Term Term [(Term, Term)]
  | Notation Term Term deriving (Eq, Ord, Show)
  -- Tactic [Term] 
   
getSeqFun :: (Term -> String) -> Term -> [String]
getSeqFun f (App b@(App _ _) a) = f a : getSeqFun f b
getSeqFun f (App v c) = [f c, f v]
getSeqFun f any = []

type VarMap = Map Int String
type TypeContext = Map Term Term
type BiTypeContext = Bimap Term Term

data Sort = Static | Expression deriving Show

data TermInfo = TermInfo {sort :: Term.Sort, var_names :: VarMap, context :: TypeContext, unifier :: TypeContext} deriving Show
type UniqueState = (Int, [Int], Set Int)

-- a uniquess term is a term associated with every value with a free variable name unique
type UTerm a = UniqueState -> TermInfo -> (a, UniqueState, TermInfo)

data Local = Local String Term TermInfo

newtype Definitions = Definitions (Map String Local) deriving Show -- A global state that shares definitions information

instance Show Local where
   show (Local st term term_inf) = show_terms term
      where
        show_terms (Pi term_name type_ body) = show_args ++ " -> " ++ show_terms body
          where
             show_args = case show_terms term_name of {
               "" -> show_terms type_;
               name -> "(" ++ name ++ " : " ++ show_terms type_ ++ ")";
             }
        show_terms (Lam var body) = "(\\" ++ show_terms var ++ " -> " ++ show_terms body ++ ")"
        show_terms app@(App _ _) = do
          let app_s = getSeqFun show_terms app
          "(" ++ init (Prelude.foldl (\ x y -> y ++ " " ++ x) "" app_s) ++ ")"
        show_terms(Var ref@(VarRef _)) = show ref
        show_terms (Var var_name@(VarName id)) =
           case Map.lookup id (var_names term_inf) of {
              Nothing -> show var_name;
              Just x -> x;
           }
        show_terms (Constr type_ ls) = "{" ++ show_terms type_ ++ ":: " ++ foldr (\x y ->  "|" ++ show_terms x ++ " " ++ y) "" ls  ++ "}"
        show_terms (Match t t' ts) =
           "(case " ++ show_terms t ++ " of " ++ show_terms t' ++ " " ++ "{" ++ Prelude.foldl (\y (x, x') -> show_terms x ++ " -> " ++ show_terms x' ++ "; " ++ y) "" ts ++ "})"
        show_terms (Notation term type_) = show_terms term ++ " :: " ++ show_terms type_
      --  show_terms (Tactic terms) = ""


-- A term to term mapping with recursion
apply :: (Term -> Term) -> Term -> Term
apply f (Pi term_name type_ body) = f (Pi term_name (apply f type_) (apply f body))
apply f (Lam var body) = f (Lam var (apply f body))
apply f (App func value) = f (App (apply f func) (apply f value))
apply f (Var name) = f (Var name)
apply f (Constr type_ constructors) = f (Constr (apply f type_) (map (apply f) constructors))
apply f (Notation term type_) = f (Notation (apply f term) (apply f type_))
--apply f (Tactic terms) = f . Tactic . map (apply f) $ terms
apply f (Match destructed type_ patterns) = f (Match (apply f destructed) (apply f type_) (map (Data.Bifunctor.second (apply f)) patterns))

-- Folding a term without recursion
foldRec :: (a -> Term -> a) -> a -> Term -> a
foldRec f k x = case x of
    Pi n x' y' -> foldRec f (foldRec f k y') x'
    Lam x y ->  foldRec f k y
    App t t' -> foldRec f (foldRec f k t) t'
    Var t' -> f k (Var t')
 --   Tactic t -> do
   --       Prelude.foldr (flip (foldRec f)) k t
    Constr t c -> do
        let x' = foldRec f k t
        Prelude.foldr (flip (foldRec f)) x' c
    Notation t t' -> foldRec f (foldRec f k t') t
    Match matched type' k' ->  do
        let x' = foldRec f (foldRec f k matched) type'
        Prelude.foldr (\ (_, x) y -> foldRec f y x) x' k'

-- Folding a term
foldTerm :: (a -> Term -> a) -> a -> Term -> a
foldTerm f k x = case x of
    Pi n x' y' -> foldTerm f (foldTerm f (f k (Pi n x' y')) y') x'
    Lam x y ->  foldTerm f (f k (Lam x y)) y
    App t t' -> foldTerm f (foldTerm f (f k (App t t')) t) t'
    Var t' -> f k (Var t')
    Notation t t' -> foldTerm f (foldTerm f (f k (Notation t t')) t) t'
   -- Tactic t -> do
    --      let x' = f k (Tactic t)
    --      Prelude.foldr (flip (foldTerm f)) x' t
    Constr t c -> do
        let x' = foldTerm f (f k (Constr t c)) t
        Prelude.foldr (flip (foldTerm f)) x' c
    Match matched type' k' ->  do
        let x' = foldTerm f (foldTerm f (f k (Match matched type' k')) matched) type'
        Prelude.foldr (\ (_, x) y -> foldTerm f y x) x' k'

-- A mapping term to term without recursion
infixr 8 ##
(##) :: (Term -> Term) -> Term -> Term
(##) f (Pi term_name type_ body) = Pi (f term_name) (f type_) (f body)
(##) f (Lam var body) = Lam (f var) (f body)
(##) f (App func value) = App (f func) (f value)
(##) f (Var name) = f (Var name)
(##) f (Constr type_ constructors) = Constr (f type_) (map f constructors)
(##) f (Notation term type_) = Notation (f term) (f type_)
(##) f (Match destructed type_ patterns) = Match (f destructed) (f type_) (map (Data.Bifunctor.second f) patterns)
--(##) f (Tactic terms) = Tactic $ map f terms

-- Unfolding a monadic term by folding a term without recursion 
infixr 8 #>>=
(#>>=) :: Monad m => (Term -> m Term) -> Term -> m Term
(#>>=) f (Pi term_name type_ body) = do
   term_nameM <- f term_name
   type_M <- f type_
   bodyM <- f body
   return (Pi term_nameM type_M bodyM)
(#>>=) f (Lam var body) = do
   varM <- f var
   bodyM <- f body
   return (Lam varM bodyM)
(#>>=) f (App func value) = do
   funcM <- f func
   valueM <- f value
   return (App funcM valueM)
(#>>=) f (Constr type_ constructors) = do
   type_M <- f type_
   constructors_M <- mapM f constructors
   return (Constr type_M constructors_M)
(#>>=) f (Notation term type_) = do
   termM <- f term
   type_M <- f type_
   return (Notation termM type_M)
(#>>=) f (Match destructed type_ patterns) = do
   destructedM <- f destructed
   type_M <- f type_
   patterns <- mapM (\(i, predicate) -> do
      pred <- f predicate
      return (i, pred)) patterns
   return $ Match destructedM type_M patterns
(#>>=) f v@(Var _) = f v
--(#>>=) f (Tactic xs) = do
 --  xsM <- mapM f xs
 ---  return (Tactic xsM)

-- Unfolding a monadic term by folding a term with recursion 
infixr 8 #>=>
(#>=>) :: Monad m => (Term -> m Term) -> Term -> m Term
(#>=>) f (Pi term_name type_ body) = do
   type_M <- f #>=> type_
   bodyM <- f #>=> body
   f (Pi term_name type_M bodyM)
(#>=>) f (Lam var body) = do
   bodyM <- f #>=> body
   f (Lam var bodyM)
(#>=>) f (App func value) = do
   funcM <- f #>=> func
   valueM <- f #>=> value
   f (App funcM valueM)
(#>=>) f (Constr type_ constructors) = do
   type_M <- f #>=> type_
   constructors_M <- mapM (f #>=>) constructors
   f (Constr type_M constructors_M)
(#>=>) f (Notation term type_) = do
   termM <- f #>=> term
   type_M <- f #>=> type_
   f (Notation termM type_M)
(#>=>) f (Match destructed type_ patterns) = do
   destructedM <- f #>=> destructed
   type_M <- f#>=> type_
   patterns <- mapM (\(i, predicate) -> do
      pred <- f #>=> predicate
      return (i, pred)) patterns
   f $ Match destructedM type_M patterns
(#>=>) f v@(Var _) = f v
--(#>=>) f (Tactic xs) = do
 --  xsM <- mapM (f #>=>) xs
  --- f (Tactic xsM)

setLocal :: Local -> Term -> Local
setLocal (Local str term term_inf) nterm = Local str nterm term_inf

unique :: a -> UTerm a
unique k state c = (k, state, c)

unionTermInfo :: TermInfo -> TermInfo -> TermInfo
unionTermInfo (TermInfo sort var context unifer) (TermInfo sort' var' context' unifer') =
     TermInfo sort' var' (Map.union context' context) (Map.union unifer' unifer)

bind  :: forall a b. UTerm a -> (a -> UTerm b) -> UTerm b
bind k f state struct = do
   let (a, state', struct') = k state struct
   let (u, rand, set_rand) = state'
   let new = uniquess_effect rand set_rand
   f a (new, tail rand, Set.insert new set_rand) (unionTermInfo struct struct')
   where
      uniquess_effect ls set = do
          let new = head ls
          if Set.member new set then uniquess_effect (tail ls) set else new

newtype Unique a = Wrap (UTerm a)

instance Functor Unique where
  fmap f (Wrap term_a) = Wrap (\state struct -> do
     let (a, state', struct') = term_a state struct
     (f a, state', unionTermInfo struct struct'))

instance Applicative Unique where
  pure a = Wrap (unique a)
  (<*>) (Wrap fab) (Wrap term_a) = Wrap (\state struct -> do
     let (a, state', struct') = term_a state struct
     let (ab, state'', struct'') = fab state' (unionTermInfo struct struct')
     (ab a, state'', unionTermInfo struct' struct''))

instance Monad Unique where
  (>>=) (Wrap term_a) f = Wrap (bind term_a (\a -> do
    let (Wrap unique) = f a
    unique
   ))

getRandState :: Unique UniqueState
getRandState = Wrap (\state struct -> (state, state, struct))

run :: Local -> Unique Term -> Term
run (Local _ term term_inf) k = do
   let effectR = rand
   let (Wrap mTerm) = k
   let (term, _, _) = mTerm (head effectR, tail effectR, Set.empty) term_inf
   term

remember :: Int -> String -> Unique ()
remember i str = Wrap (\state struct -> ((), state, struct {var_names = Map.insert i str (var_names struct)}))

updateTerm :: (Term -> Term) -> Term -> Unique ()
updateTerm f t = Wrap (\state (TermInfo sort var context unifer) ->
     ((), state, TermInfo sort var (Map.update (return . f) t context) unifer))

getTypeByContext :: Term -> Unique (Maybe Term)
getTypeByContext term = Wrap (\state struct@(TermInfo sort var context unifer) ->
     (Map.lookup term context, state, struct))

saveTermOnContext :: (Term, Term) -> Unique ()
saveTermOnContext (origin, target) = Wrap (\state struct@(TermInfo sort var context unifer) ->
     ((), state, TermInfo sort var (Map.insert origin target context) unifer))

name :: String -> Unique Int
name str = do
   id <- Wrap (\state@(u, _, _) struct -> (u, state, struct))
   remember id str
   return id

uniqueness :: Unique Int
uniqueness = Wrap (\state@(u, _, _) struct -> (u, state, struct))

substituteVarNames :: (Int,  String) -> Term -> Unique Term
substituteVarNames (i, str) term = substitute #>=> term
  where
     substitute v@(Var (VarRef name))
      | name == str = return $ Var . VarName $ i
      | otherwise = return v
     substitute l@Lam{} = do
        type_ <- getTypeByContext l
        case type_ of {
           Just k -> (do
                term <- substituteVarNames (i, str) k
                saveTermOnContext (l, term)
                return l);
           Nothing -> return l;
        }
     substitute any = return any

encodeAbstractions :: [String] -> Term -> Unique Term
encodeAbstractions [] y = return y
encodeAbstractions (x : xs) y = do
   var_name <- name x
   r <- encodeAbstractions xs y
   substituteVarNames (var_name, x) (Lam (Var . VarName $ var_name) r)

encodeMatchPredicate :: Term -> Unique (Term, [(Int, String)])
encodeMatchPredicate var@(Var (VarRef ref)) = return (var, [])
encodeMatchPredicate (App x var@(Var (VarRef ref))) = do
   name_var <- name ref
   (term, predicates) <- encodeMatchPredicate x
   return (App term (Var . VarName $ name_var), (name_var, ref) : predicates)
encodeMatchPredicate term = error "Internal error : The predicates should always carry a set of variables"

purefyPTerm :: PTerm -> Unique Term
purefyPTerm (PType term_name type_ body) = do
   term_name_v <- name term_name
   type__purified <- purefyPTerm type_
   body_purified <- purefyPTerm body
   type_branch <- substituteVarNames (term_name_v, term_name) body_purified
   return (Pi (Var . VarName $ term_name_v) type__purified type_branch)
purefyPTerm (PLam args body type_) = do
   bodyM <- purefyPTerm body
   x <- encodeAbstractions args bodyM
   case type_ of {
      Just type_ -> (do
         type__purified <- purefyPTerm type_
         return (Notation x type__purified));
      Nothing -> return x;
     }
purefyPTerm (PApp x y) = do
   purified_x <- purefyPTerm x
   purified_y <- purefyPTerm y
   return (App purified_x purified_y)
purefyPTerm (PTatic xs) = undefined 
  -- v <- mapM purefyPTerm xs
  -- return (Tactic v)
purefyPTerm (PVar s) =
   return . Var . VarRef $ s
purefyPTerm (PConstructors type_ constructors) = do
   type_M <- purefyPTerm type_
   constructors_M <- mapM purefyPTerm constructors
   return (Constr type_M constructors_M)
purefyPTerm (PMatch destructed type_ patterns) = do
   destructed_M <- purefyPTerm destructed
   type_M <- purefyPTerm type_
   patternsM <- mapM (\(predicate, body) -> do
      pred <- purefyPTerm predicate
      (predM, pred_vars) <- encodeMatchPredicate pred
      bodyM <- purefyPTerm body
      branchs <- foldr (\pair bodyM -> do
         body <- bodyM
         substituteVarNames pair body) (return bodyM) pred_vars
      return (predM, branchs)
      ) patterns
   return (Match destructed_M type_M patternsM)
purefyPTerm (PNotation term type_) = do
   termM <- purefyPTerm term
   type_M <- purefyPTerm type_
   return (Notation termM type_M)
purefyPTerm (PDef name body term) = do
   termM <- purefyPTerm term
   body <- purefyPTerm body
   let subs = Var . VarRef $ name
   return $ apply (\t -> if t == subs then body else t) termM


transform :: (Int, [Int], Set Int) -> PTerm -> Term.Sort -> (Term, UniqueState, TermInfo)
transform state term sort = do
   let (i, effectR, set) = state
   let purify_continue term = purefyPTerm term
   let (Wrap mTerm) = purify_continue term
   mTerm (i, tail effectR, set) (TermInfo sort Map.empty Map.empty Map.empty)

pureTerms :: [PDefinitons] -> ((Int, [Int], Set Int), [Local])
pureTerms [] = ((head rand, tail rand, Set.empty), [])
pureTerms ((term_name, sort, pterm) : xs) = do
   let sortT = case sort of {
      SortStatement -> Expression;
      SortStatic -> Static
   }
   let (state, locals) = pureTerms xs
   let (term, new_state, term_inf) = transform state pterm sortT
   (new_state, Local term_name term term_inf : locals)

state :: [PDefinitons] -> [(String, Local)]
state pdefs = do
   let (_, locals) = pureTerms pdefs
   foldr (\local@(Local str _ _) y -> y ++ [(str, local)]) [] locals
