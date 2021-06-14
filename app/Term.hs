
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Term where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric (showHex)

import Parser
import Effectful

data VarName = VarName Int | VarRef String deriving (Eq, Ord)

instance Show VarName where
  show (VarName i) = showHex i ""
  show (VarRef i) = i

varEmpty = VarName 0

data Term =
   Self Term Term Term Term
  | Lam Term Term
  | App Term Term
  | Var VarName
  | Tactic [Term] deriving (Eq, Ord, Show)

apply :: (Term -> Term) -> Term -> Term
apply f (Self self term_name type_ body) = f (Self self term_name (apply f type_) (apply f body))
apply f (Lam var body) = f (Lam (apply f var) (apply f body))
apply f (App func value) = f (App (apply f func) (apply f value))
apply f (Var name) = f (Var name)
apply f (Tactic terms) = f . Tactic . map (apply f) $ terms

type VarMap = Map Int String
type TypeContext = Map Term Term
type Definitions = Map String Term

data TermInfo = TermInfo {var_names :: VarMap, context :: TypeContext}
-- a uniquess term is a term associated with every value with a free variable name unique
type UTerm a = Set Int -> [Int] -> Int -> TermInfo -> (a, TermInfo)

unique :: a -> UTerm a
unique k _ _ _ c = (k, c)

bind  :: forall a b. UTerm a -> (a -> UTerm b) -> UTerm b
bind k f set ls unique struct = do
   let (a, struct') = k set ls unique struct
   let new = uniquess_effect ls
   f a (Set.insert new set) (tail ls) new struct'
   where
      uniquess_effect ls = do
          let new = head ls
          if Set.member new set then uniquess_effect (tail ls) else new

newtype Unique a = Wrap (UTerm a)

instance Functor Unique where
  fmap f (Wrap term_a) = Wrap (\set ls str struct -> do
     let (a, struct') = term_a set ls str struct
     (f a, struct'))

instance Applicative Unique where
  pure a = Wrap (unique a)
  (<*>) (Wrap fab) (Wrap term_a) = Wrap (\set ls str struct -> do
     let (a, struct') = term_a set ls str struct
     let (ab, struct''') = fab set ls str struct'
     (ab a, struct'''))

instance Monad Unique where
  (>>=) (Wrap term_a) f = Wrap (bind term_a (\a -> do
    let (Wrap unique) = f a
    unique
   ))

remember :: Int -> String -> Unique ()
remember i str = Wrap (\_ _ u struct -> ((), struct {var_names = Map.insert i str (var_names struct)}))

name :: String -> Unique Int
name str = do
   id <- Wrap (\_ _ u struct -> (u, struct))
   remember id str
   return id

assert :: (Term, Term) -> Unique ()
assert (term, target) = Wrap (\_ _ u struct -> ((), struct {context = Map.insert term target (context struct)}))

substituteVarNames :: (Int,  String) -> Term -> Term
substituteVarNames (i, str) = apply substitute
  where
     substitute v@(Var (VarRef name))
      | name == str = Var . VarName $ i
      | otherwise = v
     substitute any = any

encodeAbstractions :: [String] -> PTerm -> Unique Term
encodeAbstractions [] y = purefyPTerm y
encodeAbstractions (x : xs) y = do
   var_name <- name x 
   r <- encodeAbstractions xs y
   return (substituteVarNames (var_name, x) (Lam (Var . VarName $ var_name) r))

purefyPTerm :: PTerm -> Unique Term
purefyPTerm (PSelf self term_name type_ body) = do
   self_v <- name self
   term_name_v <- name term_name
   type__purified <- purefyPTerm type_
   body_purified <- purefyPTerm body
   let substitute_type_reference = substituteVarNames (self_v, self) . substituteVarNames (term_name_v, term_name)
   return (Self (Var . VarName $ self_v) (Var . VarName $ term_name_v) type__purified (substitute_type_reference body_purified))
purefyPTerm (PLam args body type_) = do
   x <- encodeAbstractions args body
   type__purified <- purefyPTerm type_
   assert (x, type__purified)
   return x
purefyPTerm (PApp x y) = do
   purified_x <- purefyPTerm x
   purified_y <- purefyPTerm y
   return (App purified_x purified_y)
purefyPTerm (PTatic xs) = do
   v <- mapM purefyPTerm xs
   return (Tactic v)
purefyPTerm (PVar s) = do
   return . Var . VarRef $ s
purefyPTerm (PMatch _ _ _) = undefined 

transform :: PTerm -> (Term, TermInfo)
transform term = do
   let effectR = rand
   let (Wrap mTerm) = purefyPTerm term
   mTerm Set.empty (tail effectR) (head effectR) (TermInfo Map.empty Map.empty)

data Local = Local String Term TermInfo
data State = State {defs :: Definitions, locals :: [Local]} -- A global state that shares definitions information

pureTerms ::  [PDefinitons] -> [Local]
pureTerms [] = []
pureTerms ((term_name, pterm) : xs) = do
   let (term, term_inf) = transform pterm
   Local term_name term term_inf : pureTerms xs

state :: [PDefinitons] -> State
state pdefs = do
   let locals = pureTerms pdefs
   let defs = foldr (\(Local str term _) y -> Map.insert str term y) Map.empty locals
   State defs locals