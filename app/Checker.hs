{-# LANGUAGE LambdaCase #-}
module Checker where
import Term
import Debug.Trace
import Data.Map (Map)

import Control.Monad
import Data.Maybe
import Data.Bifunctor
import Control.Applicative
import Data.List
import Util
import Data.Functor ( (<&>) )

import qualified Data.Map as Map
type LocalM a = Definitions  -> Local -> (a, Definitions, Local)
newtype ContextM a = ContextM (LocalM a)

data Checker = Checker {error_msg :: [String], hole_msg :: [String]} deriving Show

data Jugdment = Jugdment Term Term

unique :: a -> LocalM a
unique a state local = (a, state, local)

bind :: LocalM a -> (a -> LocalM b) -> LocalM b
bind local_a f state local = do
        let (a, locally, st) = local_a state local
        f a locally st

instance Functor ContextM where
  fmap f (ContextM local_a) =
          ContextM (\state local -> do
          let (a, st, locally) = local_a state local
          (f a, st, locally)
   )

instance Applicative ContextM where
    pure a = ContextM (Checker.unique a)
    (<*>) (ContextM local_fab) (ContextM local_a) = ContextM (\state local -> do
            let (a, st, locally) = local_a state local
            let (ab, st', locally') = local_fab state locally
            (ab a, st', locally'))

instance Monad ContextM where
   (>>=) (ContextM local_a) f = ContextM (Checker.bind local_a (\a -> let (ContextM local_b) = f a in local_b))

betaSubstitution :: (Term, Term) -> Term -> Term
betaSubstitution tuple@(u, _) abs@(Lam x y) =
        if x == u then abs
        else Lam (betaSubstitution tuple x) (betaSubstitution tuple y)
betaSubstitution (u, u') v'@(Var _) = if v' == u then u' else v'
betaSubstitution u any = betaSubstitution u ## any

getTerm :: ContextM Term
getTerm = ContextM (\state l@(Local _ term _) -> (term, state, l))

getLocal :: ContextM Local
getLocal = ContextM (\state l -> (l, state, l))

getLocalName :: ContextM String
getLocalName = ContextM (\state l@(Local name _ _) -> (name, state, l))

setLocal :: Term -> ContextM Local
setLocal term = ContextM (\state l@(Local def term' term_inf) -> (Local def term term_inf, state, l))

addVarReferences :: VarMap -> ContextM ()
addVarReferences varmap = ContextM (\state (Local def term' (TermInfo sort references types unifier)) ->
    ((), state, Local def term' (TermInfo sort (Map.union references varmap) types unifier)))

shareTypes :: TypeContext -> ContextM ()
shareTypes context = ContextM (\state (Local def term' (TermInfo sort references types unifier)) ->
    ((), state, Local def term' (TermInfo sort references (Map.union types context) unifier)))

getState :: ContextM Definitions
getState = ContextM (\state l@(Local _ term _) -> (state, state, l))

setState :: Local -> ContextM Definitions
setState local = ContextM (\state _ -> (state, state, local))

getDef ::  String -> ContextM (Maybe Local)
getDef ref = do
        (Definitions map) <- getState
        return $ Map.lookup ref map

getStaticSymbol ::  String -> ContextM (Maybe Local)
getStaticSymbol ref = do
        (Definitions map) <- getState
        case Map.lookup ref map of {
          Just l@(Local _ term (TermInfo Static _ _ _) )-> return $ Just l;
          _ -> return Nothing;
        }

getDefType :: String -> ContextM (Maybe Term)
getDefType ref = do
        value <- getDef ref
        case value of {
          Just (Local _ term (TermInfo Expression varmaps context _)) -> (do
                  addVarReferences varmaps
                  case term of {
                    Notation term type_ -> return $ Just type_;
                    _ -> return $ Map.lookup term context;
                  });
          Just (Local _ term (TermInfo Static varmaps context _)) -> (do
                  addVarReferences varmaps
                  return $ Just term);
          _ -> return Nothing;
        }

getRef :: String -> ContextM (Maybe Term)
getRef ref = do
        value <- getDef ref
        case value of {
          Just (Local _ x (TermInfo Expression v c _)) -> addVarReferences v >> shareTypes c >> return (Just x);
          _ -> return Nothing;
        }

getMapContext :: ContextM TypeContext
getMapContext = ContextM (\state l@(Local _ _ (TermInfo _ _ context _)) -> (context, state, l))

getUnifier :: ContextM TypeContext
getUnifier = ContextM (\state l@(Local _ _ (TermInfo _ _ _ unifier)) -> (unifier, state, l))

getTermUnification :: Term -> ContextM (Maybe Term)
getTermUnification term = ContextM (\state l@(Local _ _ (TermInfo _ _ _ unifier)) -> (Map.lookup term unifier, state, l))

insertUnification :: (Term, Term) -> ContextM ()
insertUnification (origin, target) =  ContextM (\state (Local def term' (TermInfo sort references types unifier)) ->
    ((), state, Local def term' (TermInfo sort references types (if target == origin then unifier else Map.insert origin target unifier))))

unify :: (Term, Term) -> ContextM ()
unify (target, origin) = do
   cicleTerm <- getTermUnification origin
   case cicleTerm of {
        Nothing -> insertUnification (origin, target);
        Just k -> do
                insertUnification (target, k);
                insertUnification (origin, target);
   }

getContextType :: Term -> ContextM (Maybe Term)
getContextType k = Map.lookup k <$> getMapContext

setContextType :: (Term, Term) -> ContextM ()
setContextType (k, y) =
  ContextM (\state (Local name term (TermInfo sort vars context unifier)) -> ((), state, Local name term (TermInfo sort vars (Map.insert k y context) unifier)))

clearUnifer :: ContextM ()
clearUnifer =
    ContextM (\state (Local name term (TermInfo sort vars context _)) -> ((), state, Local name term (TermInfo sort vars context Map.empty)))

setUnifer :: TypeContext -> ContextM ()
setUnifer unifier =
  ContextM (\state (Local name term (TermInfo sort vars context _)) -> ((), state, Local name term (TermInfo sort vars context unifier)))

setTerm :: Term -> ContextM ()
setTerm term = ContextM (\state l@(Local x _ z) -> ((), state, Local x term z))

saveTerm :: ContextM Term -> ContextM ()
saveTerm m = do
        term <- m
        setTerm term

contextMrun :: ContextM a -> Definitions -> Local -> (a, Definitions, Local)
contextMrun (ContextM c) = c

isTypeUniverse :: Term -> Bool
isTypeUniverse (Var (VarRef name)) = name == "Type"
isTypeUniverse _ = False

isSetUniverse :: Term -> Bool
isSetUniverse (Var (VarRef name)) = name == "*"
isSetUniverse _ = False

isKindUniverse :: Term -> Bool
isKindUniverse (Var (VarRef name)) = name == "Kind"
isKindUniverse _ = False

isHole:: Term -> Bool
isHole (Var (VarRef name)) = name == "__"
isHole _ = False

typeUniverse :: Term
typeUniverse = Var (VarRef "Type")

kindUniverse :: Term
kindUniverse = Var (VarRef "Kind")

substitutePiVars :: (Term, Term) -> Term
substitutePiVars (Pi var type_ body, Lam var' body') =
   Pi var' type_ (apply (\x -> if x == var then var' else x) (substitutePiVars (body, body')))
substitutePiVars (pi, _) = pi

getFun :: Term -> ContextM (Maybe Term)
getFun (App b@(App _ _) a) = getFun b
getFun (App v@(Var (VarRef ref)) _) = getRef ref
getFun v = return Nothing

removeTypeConstructors :: Term -> Term
removeTypeConstructors (Constr type_ _) = type_
removeTypeConstructors any = any

getConstructor :: Term -> ContextM (Maybe Local)
getConstructor (App b@(App _ _) a) = getConstructor b
getConstructor (App v@(Var (VarRef ref)) _) = getStaticSymbol ref
getConstructor  (Var (VarRef ref)) = getStaticSymbol ref
getConstructor v = return Nothing

checkMatchReduction :: Term -> (Bool, Bool)
checkMatchReduction = rec_match
      where
        rec_match (App x y) = rec_match x `bind` rec_match y
        rec_match (Lam x y) = rec_match y
        rec_match (Constr type_ body) =
                rec_match type_
        rec_match (Pi var type_ body) = rec_match type_ `bind` rec_match body
        rec_match (Notation term type') = rec_match term `bind` rec_match type'
        rec_match (Match (Notation destructed _) type_ patterns) = rec_match $ Match destructed type_ patterns
        rec_match m@Match{} = (False, not (checkIfUnstuck m))
        rec_match (Var ref) = (True, True)
        bind (x, y) (x', y') = (x && x', y && y')

checkPredicateTypeConstructor  :: Term -> Term -> Bool
checkPredicateTypeConstructor y k = case (y, k) of
   (_, App k2 k2') -> True
   (Var (VarRef "_"), _) -> True  -- On (P _) against (P' y)
   (_ , Var (VarName _)) -> True -- On (P' y) against (P c) 
   (v@(Var _), v'@(Var _)) -> v == v'
   _ -> False

checkPredicateMatching :: Term -> Term -> Bool
checkPredicateMatching k y =  case (y, k) of -- The pair (predicate, destructured)
        (App k k', App k2 k2') -> checkPredicateMatching k2 k && checkPredicateMatching k2' k'
        (Var (VarName _), _) -> True
        (Var (VarRef v), Var (VarRef v')) -> v == v'
        _ -> False

checkIfUnstuck :: Term -> Bool
checkIfUnstuck k = case k of
        Match matched _ terms -> do
            let n = Prelude.foldl (\ y (predicate, term) -> if checkPredicateMatching matched predicate then (predicate, term) : y else y) [] terms
            not (null n)
        _ -> False

destructMatching :: Term -> Term -> Term -> Term
destructMatching matched construction term' = do
        let substuitions = get_match_composition matched construction []
        let substitute_def term' (k, u) = matching_var_substituion term' (k, u)
        Prelude.foldl (\ y (u, x') -> substitute_def y (u, x')) term' substuitions
            where
                get_match_composition k y ls = case (y, k) of
                    (App x x', App u u') -> get_match_composition u x (get_match_composition u' x' ls)
                    (Var (VarName i), n) -> (Var (VarName i), n) : ls
                    _ -> ls
                get_vars_match predicate = foldTerm (\ y x -> case x of {v@(Var _) -> v : y; _ -> y}) [] predicate
                matching_var_substituion (Match matched type' k') u_@(u, _) = do
                       let same_mvar term = Prelude.foldl (\ y var -> y || u == var) False (get_vars_match term)
                       let terms' = Prelude.map (\(predicate, term) -> (predicate, if same_mvar predicate then term else matching_var_substituion term u_)) k'
                       Match (matching_var_substituion matched u_) (matching_var_substituion type' u_) terms'
                matching_var_substituion v'@(Var i) (u, u') = if v' == u then u' else v'
                matching_var_substituion k u = (`matching_var_substituion` u) ## k

evalMatch :: Term -> Term
evalMatch (Match matched type' terms) = do
        let n = Prelude.foldl (\ y (predicate, term) -> if checkPredicateMatching matched predicate then (predicate, term) : y else y) [] terms
        case n of
            ((construction, term') : xs) -> destructMatching matched construction term' -- by sequence of matching take the head of the matching
            [] -> Match matched type' terms
evalMatch x = x

checkResolvableMatch  :: Term -> Bool
checkResolvableMatch = foldTerm (\ x y -> not (checkIfUnstuck y) && x) True

expandFunction :: Term -> Term -> Term
expandFunction (App b@(App _ _) a) u = App (expandFunction b u) a
expandFunction (App v@(Var _) l) u = App u l
expandFunction v u = v

piReduction :: (Term, Term) -> Term
piReduction (Pi var n y, t) = apply (\x -> if x == var then t else x) y
piReduction (pi, _) = pi

reduceBetaVariables :: Term -> Term
reduceBetaVariables = forceBetaReduction
      where
        forceBetaReduction app@(App (Notation x _) y) = forceBetaReduction $ App x y
        forceBetaReduction (App (Lam x y) y') = betaSubstitution (x, forceBetaReduction y') y
        forceBetaReduction term = term

isMatch :: Term -> Bool
isMatch Match {} = True
isMatch _ = False

normalize :: Term -> ContextM Term
normalize term = do
        (check, norm_term) <- eagerStep term
        if check then do
           term_ <- showTerm norm_term
           trace term_ (return ())
           normalize norm_term
        else
           return norm_term
  where
    eagerStep :: Term -> ContextM (Bool, Term)
    eagerStep t@(App(Lam x y) y') = do
            (b, y) <- eagerStep y
            (b', y') <- eagerStep y'
            (b''', rec_) <- eagerStep (betaSubstitution (x, y') y)
            return (True, rec_)
    eagerStep t@(App (Notation term _) y') = eagerStep (App term y')
    eagerStep t@(App x y) = do
      (check, recur) <- do
              (check_x, x_M) <- case x of {
                Var _ -> return (False, x);
                _ -> eagerStep x
              } -- do not unfold (App (Var _) ...) for distinguish (App (Var _) _) of (Var _) in eagerStep pattern matching
              y_M <- normalize y
              return (check_x, App x_M y_M)
      fun <- getFun t
      case fun of {
        Just v' -> (do
          v' <- normalize v'
          let definitional_term = reduceBetaVariables (expandFunction recur v')
          let (matchs, resolvable_match) = checkMatchReduction definitional_term
          if matchs == resolvable_match then do
            return (True, definitional_term)
          else
            return (check, recur));
          Nothing -> return (check, recur);
        }
    eagerStep v@(Var (VarRef name)) = do
            term <- getRef name >>= mapM eagerStep
            case term of {
              Just k -> return (True, snd k);
              Nothing -> return (False, v);
            }
    eagerStep m@(Match (Notation matched type_) type' k') = eagerStep $ Match matched type' k'
    eagerStep m@(Match matched type' k') = do
            (checker, matchedM) <- eagerStep matched
            (checker', type'M) <- eagerStep type'
            let match = Match matchedM type'M k'
            if checkIfUnstuck match then do
               return (True, evalMatch match)
             else
               return (checker || checker', match)
    eagerStep (Lam abs body) = do
            (checker, bodyM) <- eagerStep body
            return (checker, Lam abs bodyM)
    eagerStep (Constr type_ constructors) = do
            (checker, type_M) <- eagerStep type_
     --     constructors_M <- mapM normalize constructors
            return (checker, Constr type_M constructors)
    eagerStep (Pi var type_ body) = do
            (checker, typeM) <- eagerStep type_
            (checker', bodyM) <- eagerStep body
            return (checker || checker', Pi var typeM bodyM)
    eagerStep (Notation term type_) =
            return (False, Notation term type_)
    eagerStep v = return (False, v)

pushTypeError :: String -> Checker -> ContextM Checker
pushTypeError error checker = do
        name <- getLocalName
        return checker {error_msg = error : error_msg checker}

isRef :: Term -> Bool
isRef (Var (VarRef _)) = True
isRef _ = False

isVarName :: Term -> Bool
isVarName (Var (VarName  _)) = True
isVarName _ = False

pushHoleMsg :: String -> Checker -> ContextM Checker
pushHoleMsg error checker =
        return checker {hole_msg = error : hole_msg checker}

pushLeakType :: Term -> Term -> Checker -> ContextM Checker
pushLeakType bad_typed helper checker = do
        name <- getLocalName
        lacks_type <- showTerm bad_typed
        helper <- showTerm helper
        if isHole bad_typed then
          return checker
        else do
          let ref_msg = if isRef bad_typed then ", maybe you forgot to move the definition " ++ lacks_type ++ " to under " ++ name else ""
          return checker {error_msg =
          ("The term " ++ lacks_type++ " lacks of type term" ++ " in " ++ helper ++ ref_msg) : error_msg checker}

showTerm :: Term -> ContextM String
showTerm term = do
        term <- return term
        local <- Checker.setLocal term
        return (show local)

checkSubs :: Term -> ContextM Bool
checkSubs = foldTerm (\a_M term -> do
            a <- a_M
            uni <- getTermUnification term
            return $ isJust uni || a) (return False)

matchingSubs:: Term -> ContextM Term
matchingSubs term = do
        subs <- checkSubs term
        if subs then
                do
                  term <- (\term -> do
                          uni <- getTermUnification term
                          case uni of {
                            Just x -> return x;
                            Nothing -> return term;
                            }) #>=> term
                  matchingSubs term
        else return term

piUniquess :: Term -> Unique Term
piUniquess term = case term of {
        Pi v type_ body -> (do
                unique_abs <- uniqueness
                type_M <- piUniquess type_
                bodyM <- piUniquess body
                let new_var = Var $ VarName unique_abs
                return $ Pi new_var type_M (substituteVarNames (new_var, v) bodyM));
        Lam v body -> (do
                unique_abs <- uniqueness
                body_M <- piUniquess body
                let new_var = Var $ VarName unique_abs
                return $ Lam new_var (substituteVarNames (new_var, v) body_M));
        var@(Var _) -> return var;
        term -> piUniquess #>>= term;
        }
  where
          substituteVarNames (new, old_ref) term = apply (\x -> if x == old_ref then new else x) term

equalTerms :: Checker -> Term -> Term -> (Term, Term) -> ContextM (Bool, Checker)
equalTerms checker term helper (origin@(Constr type' constructors), target@(Constr type'' predicates))  = do
            checker <- checkTypeClauses helper (constructors, predicates) origin checker  -- subtyping rule
            (b', checker) <- equalTerms checker term helper (type', type'')
            return (b', checker)
equalTerms checker term helper (origin@(Constr type' _), target) = do  -- subtyping rule
            (b', checker) <- equalTerms checker term helper (type', target)
            return (b', checker)
equalTerms checker term helper (origin, target@(Constr type' _)) = do  -- subtyping rule
   stringfy_term <- showTerm term
   stringfy_helper <- showTerm helper
   stringfy_origin <- showTerm origin
   stringfy_type' <- showTerm type'
   checker <- pushTypeError
     ("The term " ++ stringfy_term ++ " can not be \ndowngrade to : " ++ stringfy_type' ++ "\ninstead of :" ++ stringfy_origin ++ "\nwhere : " ++ stringfy_helper ++ " is your jugdment") checker
   return (False, checker)
equalTerms checker term helper (App x y, App x' y') = do
   (b, checker) <- equalTerms checker term helper (x, x')
   (b', checker) <- equalTerms checker term helper (y, y')
   return (b && b', checker)
equalTerms checker term helper (Lam x y, Lam x' y') = do
  (b, checker) <- equalTerms checker term helper (x, x')
  (b', checker) <- equalTerms checker term helper (y, y')
  return (b && b', checker)
equalTerms checker term helper (Pi n x y, Pi n' x' y') = do
  (b1, checker) <- equalTerms checker term helper (n, n')
  (b2, checker) <- equalTerms checker term helper (x, x')
  (b3, checker) <- equalTerms checker term helper (y, y')
  return (b1 && b2 && b3, checker)
equalTerms checker term helper (Notation body _, Notation body' _) = equalTerms checker term helper (body, body')
equalTerms checker term helper (Notation body _, body') = equalTerms checker term helper (body, body')
equalTerms checker term helper (body, Notation body' _) = equalTerms checker term helper (body, body')
equalTerms checker term helper (Match n x y, Match n' x' y') = do
  (b1, checker) <- equalTerms checker term helper (n, n')
  (b2, checker) <- equalTerms checker term helper (x, x')
  case (y, y') of {
    (p : ys, p' : ys') -> (do
      (b3, checker) <- equalTerms checker term helper (fst p, fst p')
      (b4, checker) <- equalTerms checker term helper (snd p, snd p')
      return (b1 && b2 && b3 && b4, checker));
    ([], []) -> return (b2, checker);
    _ -> return (False, checker);
  }
equalTerms checker term helper (origin, target) = return (origin == target, checker)

piIdentity :: Term -> ContextM Term
piIdentity pi = do
        pi_local <- Checker.setLocal pi
        return $ run pi_local (piUniquess pi)

piEquality ::  Term -> Term -> Checker -> (Term, Term) -> ContextM (Bool, Checker)
piEquality term helper checker (origin, target) = do
        unique_origin <- piIdentity origin
        unique_target <- piIdentity target
        normalized_origin <- simpl unique_origin
        normalized_target <- simpl unique_target
      --  (unique_eq, checker') <- equalTerms checker term helper (unique_origin, unique_target)
        (normalized_eq, checker) <- equalTerms checker term helper (normalized_origin, normalized_target)
        return (normalized_eq, checker)

getType :: Term -> ContextM (Maybe Term)
getType term =
        do
          lookup_env <- lookup_type_on_env
          lookup_context <- lookup_type_on_context
          universeType <- isUniverse
          let term = typeNotation <|> lookup_env <|> lookup_context <|> universeType
          return term
   where
     lookup_type_on_env =
       case term of {
         Var (VarRef ref) -> getDefType ref;
         _ -> return Nothing;
       }
     lookup_type_on_context = getContextType term
     typeNotation = case term of {
         Notation _ type_ -> Just type_;
         _ -> Nothing;
     }
     isUniverse
       | isTypeUniverse term =
        return $ Just (Var (VarRef "Kind"))
       | isSetUniverse term =
       return $ Just typeUniverse
       | otherwise =
       return Nothing

setType :: Jugdment -> ContextM ()
setType (Jugdment term type') = do
        norm_term <- simpl term
        setContextType (term, type')
        setContextType (norm_term, type')

renewType :: Term -> ContextM () -- useful after a unification with no cost to typecheck the whole term
renewType term = do
        type_ <- getType term
        mapM_ (setType . Jugdment term) type_

matchConstructors :: String -> [Term] -> ContextM Bool
matchConstructors name = foldr (\constr b_M -> do
        def <- getConstructor constr
        b <- b_M
        case def of {
                Just (Local name_constr _ _) -> return $ name_constr == name || b;
                _ -> return b;
        }) (return False)

matchConstructorOptionalType :: Checker -> String -> ([Term], Term) -> Term -> ContextM Checker
matchConstructorOptionalType checker constructor_name (constructors, type_) helper  = do
 sub <- matchConstructors constructor_name constructors
 if sub then
   return checker
 else do
   stringfyConstructor <- showTerm helper
   stringfyConstrs <- showTerm type_
   pushTypeError ("Constructor " ++ constructor_name ++ " do not belongs to " ++ stringfyConstrs ++ " in " ++ stringfyConstructor) checker;

constrSubtType :: Checker -> (Term, Term) -> Term -> Term -> ContextM Checker
constrSubtType checker pair un_norm helper = infer_constr pair
  where
    infer_constr (constructor, constrs@(Constr type' constructors)) = do
       constructor <- simpl constructor -- fix it here

       type_constructor <- getType constructor
       constr <- getConstructor constructor
       case constr of {
         Just (Local name term _) -> (do
               --  checker <- assertType (Jugdment un_norm type') constructor checker 
                 sub <- matchConstructors name constructors
                 if sub then do
                  type_app_constructor <- getType constructor
             --     show_t <- mapM showTerm type_app_constructor
           --       show_cons <- showTerm constructor
         --         trace (show (show_t, show_cons)) return ()
                  case type_app_constructor of {
                     Just type'' -> assertTypeEquality (type'', type') constructor constrs checker;
                     Nothing -> pushLeakType constructor helper checker;
                   }
                 else do
                   stringfyConstructor <- showTerm helper
                   stringfyConstrs <- showTerm constrs
                   pushTypeError ("Constructor " ++ name ++ " do not belongs to " ++ stringfyConstrs ++ " in " ++ stringfyConstructor) checker);
         _ -> do
           --     checker <- typeRules checker constructor
                case type_constructor of {
                  Just constr@(Constr type'' constructors') -> assertTypeEquality (constr, constrs) constructor helper checker;
                  Just type_ -> assertTypeEquality (type_, un_norm) constructor helper checker;
                  Nothing -> do
                        stringfy_constructor <- showTerm constructor
                        stringfy_type <- showTerm type'
                        if isHole constructor then do
                          strigfy_constructors <- mapM showTerm constructors
                          if not $ null strigfy_constructors then do
                            pushHoleMsg ("The hole expects a constructor of " ++ intercalate " or " strigfy_constructors ++ " of type " ++ stringfy_type) checker
                          else
                            pushHoleMsg ("The hole expects a falsity of type " ++ stringfy_type) checker
                        else
                          pushTypeError ("Impossible infer the Constructor " ++ stringfy_constructor ++ " type") checker
                }
               -- pushTypeError ("Constructor " ++ stringfy_app ++ " is not a static constructor") checker
       }
    infer_constr _ = pushTypeError "Expected a constructor" checker


simpl :: Term -> ContextM Term
simpl term = do
               term <- matchingSubs term >>= normalize
               subs <- checkSubs term
               if not subs then return term else simpl term

debugUni :: ContextM [String]
debugUni = do
        uni <- getUnifier
        mapM (\(a,b) -> do
                a' <- getType a
                a' <- mapM showTerm a'
                b' <- getType b
                b' <- mapM showTerm b'
                a <- showTerm a
                b <- showTerm b
                return (a ++ " : " ++ b ++ " >> " ++ show (a', b'))) (Map.toList uni)

assertTypeEquality :: (Term, Term) -> Term -> Term -> Checker -> ContextM Checker
assertTypeEquality (origin, target) term helper checker =
        let type_error term type_ helper k = do
                stringfy_term <- showTerm term
                stringfy_type_ <- simpl type_ >>= showTerm
                stringfy_helper <- showTerm helper
                stringfy_k <- simpl k >>= showTerm
                uni <- getUnifier
                showUni <- debugUni
                return $ "The term " ++ stringfy_term ++ ":\nshould be a type : " ++ stringfy_type_ ++ "\ninstead of : " ++ stringfy_k ++ "\n where : " ++ stringfy_helper ++ " is your jugdment\n" -- ++ intercalate "\n" showUni
         in do
         let pi_eq = piEquality term helper
       --  unified_k <- matchingSubs origin
       --  unified_type_ <- matchingSubs target
         (eq, checker) <- pi_eq checker (origin, target)
         if eq then return checker else do
                 type_error <- type_error term target helper origin
                 pushTypeError type_error checker

assertExpressionType :: Jugdment -> Term -> Checker -> ContextM Checker
assertExpressionType (Jugdment term type_) helper checker =
        if isHole term then do
          stringfy_type <- simpl type_ >>= showTerm
          setType (Jugdment term type_)
          pushHoleMsg ("The hole expects " ++ stringfy_type ++ " type") checker
        else do
          goal_type <- getType term
          case goal_type of {
            Just k -> assertTypeEquality (k, type_) term helper checker;
            Nothing -> pushLeakType term helper checker;
          }

assertType :: Jugdment -> Term -> Checker -> ContextM Checker
assertType (Jugdment term target) helper checker = do
        target <- simpl target
        assert (Jugdment term target)
 where
   assert (Jugdment term constr@(Constr _ _)) = constrSubtType checker (term, constr) target helper
   assert jugde = assertExpressionType jugde helper checker

inferByApplication :: Term -> Checker -> ContextM Checker
inferByApplication k checker  = case k of {
        app@(App x y) -> (do
                checker <- inferByApplication x checker
                checker <- inferByApplication y checker
                type_ <- getType x
                case type_ of {
                        Just pi@(Pi n term term_dependent) -> (do
                                let redPi = piReduction (pi, y)
                                setType (Jugdment y term)
                                setType (Jugdment app redPi)
                                return checker;
                        );
                        _ -> (do
                                stringify_x <- showTerm  x
                                stringify_y <- showTerm y
                                pushTypeError ("The PI-type of " ++ stringify_x ++  "can't be inferred on " ++ stringify_y ++ " construction") checker
                        )
                });
        var@(Var _) -> return checker;
        _ -> error "Internal error : infer can ony be derived by a application or var";
        }


matchUnification :: Term -> Term -> Term -> Checker -> ContextM Checker
matchUnification x u k checker = do
        type_x <- getType x
        type_u <- getType u
        case (type_x, type_u) of {
                (Just y, Just y') -> (do
                        term <- getTerm
                        y <- simpl y
                        y' <- simpl y'
                        let eq = x == u
                        unless eq $ unify (u, x) -- really implies the k axiom 
                        typeConstruction (removeTypeConstructors y) (removeTypeConstructors y')
                        uni <- getUnifier
                        mapM_ (renewType . snd) (Map.toList uni) -- renew the predicates type in the context but now with possible unification in the variables
                        assertType (Jugdment x y) term checker

                );
                _ ->  do
                      stringify_x <- showTerm x
                      stringify_u <- showTerm u
                      stringify_k <- showTerm k
                      pushTypeError ("Impossible of infer the " ++ stringify_x ++ " and " ++ stringify_u ++ " in " ++ stringify_k) checker
        }

typeConstruction :: Term -> Term -> ContextM ()
typeConstruction x y = case (x, y) of {
        (App k k', App k0 k0') -> (do
                let eq = k' == k0'
                unless eq $ do
                       typeConstruction k k0
                      -- typeConstruction k' k0' -- Unification is not injective
                       unify (k', k0')
        );
        (v@(Var (VarName _)), v') -> return ();
        t -> return ();
}

checkMatchBody :: Term -> Term -> (Term, Term) -> Checker -> ContextM Checker
checkMatchBody destructed type_ (predicate, body) checker = do
        checker <- inferByApplication predicate checker
        matchUnification destructed predicate body checker

varRule :: Checker -> Term -> ContextM Checker
varRule checker t = do
        type_ <- getType t
        case type_ of {
                Just x -> (do
                        show_term <- showTerm t
                        show_type <- showTerm x
                        return checker);
                Nothing -> do
                     term <- getTerm
                     pushLeakType t term checker
        }


piUnification :: (Term, Term) -> Term
piUnification (pi@(Pi var type_ body), abs@(Lam var' body')) = Pi var' type_ $ apply (\x -> if x == var then var' else x) (piUnification (body, body'))
piUnification (pi, _) = pi

-- Often a lambda is written as | x y :: Nat -> Nat -> Nat, in case of not having y :: Nat -> Nat, infer by 
-- the last nested lambda, if there is enough type information let's as it is
inferLambda :: Term -> ContextM ()
inferLambda abs@(Lam x _M) = do
             pi <- getType abs
             case pi of {
               Just all@Pi {} -> (do
                       all <- simpl (piUnification (all, abs))
                       setType (Jugdment abs all)
                       let (Pi _ _A _B) = all
                       setType (Jugdment x _A) -- inference ↑
                       infer_omited_notation _M _B);
               _ -> return ();
             }
  where
    infer_omited_notation _M _B = case _M of {
      lam@(Lam _ _ ) -> (do
              pi_M <- getType lam
              case pi_M of {
                Just x -> return ();
                Nothing -> setType (Jugdment lam _B);
                });
       _ -> return ()
      }
inferLambda _ = error "Internal Error : Lambda inference always must be applyed to a nested lambda"

absRule :: Checker -> Term -> ContextM Checker
absRule checker t = abs_type t
  where
    abs_type lam@(Lam x _M) = do
             pi <- getType lam
             case pi of {
               Just all@(Pi pi_x _A _B) -> (do
                       term <- getTerm
                       checker <- typeRules checker all
                       assertType (Jugdment _M _B) term checker;
                );
                Just type' -> (do
                        t_show <- showTerm lam
                        type'_show <- showTerm type'
                        pushTypeError ("You have a function : " ++ t_show ++ ", but " ++ type'_show  ++ " isn`t a PI-Type, maybe you forgot to add your arguments in your type function") checker);
                Nothing -> do
                        t_show <- showTerm t
                        term <- getTerm
                        pushLeakType lam term checker
             }
    abs_type _ = error "Internal Error : Abs Rule always must be applyed to a lambda abstract"


inferPi :: Term -> ContextM ()
inferPi pi@(Pi var_name type_var term_dependent) =
        do
            setType (Jugdment var_name type_var)
            setType (Jugdment pi typeUniverse)
inferPi _ = error "Internal Error : Pi inference always must be applyed to a Pi-Type"

prodRule :: Term -> Checker -> ContextM Checker
prodRule t checker = pi_typed_env t
  where
    pi_typed_env pi@(Pi var_name type_var term_dependent) = do
            type_ <- getType type_var
            let error_universe var_name uni = do
                    stringfy_pi <- showTerm pi
                    stringfy_var <- showTerm var_name
                    pushTypeError (stringfy_var ++ " must be a " ++ intercalate "/" uni ++ " where " ++ stringfy_pi ++ " is your jugdment") checker
            case type_ of {
              Just type' -> if isTypeUniverse type' || isSetUniverse type' then do
                              type_dependent <- getType term_dependent
                              case type_dependent of {
                                Just type_dependent -> if isUniverse type_dependent then
                                                         return checker
                                                      else
                                                         error_universe term_dependent ["Type", "Set", "Kind"];
                                Nothing  -> pushLeakType term_dependent pi checker
                              }

                            else
                              error_universe type_var ["Type", "Set"];
              Nothing -> pushLeakType var_name pi checker
            }

            where
                    isUniverse term = isTypeUniverse term || isSetUniverse term || isKindUniverse term

    pi_typed_env _ = error "Internal Error : Pi Rule always must be applyed to a Pi-Type"


appRule :: Checker -> Term -> ContextM Checker
appRule checker = app_typed
  where
    app_typed app@(App _M _N) = do
            type_ <- getType _M
            type_ <- mapM simpl type_
            case type_ of {
            Just pi@(Pi x _A _B) -> (do
                    checker <- assertType (Jugdment _N _A) app checker
                    setType $ Jugdment app (piReduction (pi, _N))
                    return checker
                    );
             Just x -> (do
                        _M_show <- showTerm _M
                        _M_x <- showTerm x
                        pushTypeError ("The type of " ++ _M_show ++ " is " ++ _M_x ++ " however this should be a Pi type (Maybe you applied more arguments than function have") checker
                       );
             Nothing -> (do
                     term <- getTerm
                     pushLeakType app term checker);
    }
    app_typed _ = error "Internal Error : App Rule always must be applyed to a application"

checkAgainstTypeConstructors :: Term -> Term -> Term -> Checker -> ContextM Checker
checkAgainstTypeConstructors constructor type' term checker = do
        type_constructor <- get_type_constructor constructor
        case type_constructor of {
                Just type_constructor -> (do
                        let pi_type = constructor_pi type_constructor
                        type' <- simpl type' <&> removeTypeConstructors
                        if checkPredicateTypeConstructor pi_type type' then
                                return checker
                        else do
                          constructor_show <- showTerm constructor
                          pi_show <- showTerm pi_type
                          type'show <- showTerm type'
                          pushTypeError ("Impossible unify " ++ pi_show ++ " with " ++ type'show ++ " on " ++ constructor_show ++ ", fail to create type constructor") checker);
                    Nothing -> do
                            constructor_show <- showTerm constructor
                            term_show <- showTerm term
                            pushTypeError ("Impossible of infer " ++ constructor_show ++ " clause on " ++ term_show ++ " fail to construct the type constructor") checker
                 }
  where
    get_type_constructor app = do
            constr <- getConstructor app
            case constr of {
                    Just (Local _ type_ _) -> return $ Just type_;
                    Nothing -> return Nothing;
            }
    constructor_pi pi@(Pi var type_ body) = constructor_pi $ piReduction (pi, Var $ VarRef "_")
    constructor_pi pi = pi

clauseChecker :: Checker -> Term -> [Term] -> Term -> ContextM Checker
clauseChecker checker match predicates term = do
        constr <- getType term >>= mapM simpl
        case constr of {
           (Just constr@(Constr _ constructors)) -> checkTypeClauses constr (constructors, predicates) match checker;
           (Just type_) -> (do
                   type_ <- simpl type_
                   constructor <- getConstructor term
                   case constructor of {
                     Just (Local name term' _) -> (do
                              let infer_constr = [generalize_constructor term]
                              checkTypeClauses (Constr type_ infer_constr) (infer_constr, predicates) match checker
                             );
                     _ ->  (do
                              stringfy_match <- showTerm match
                              stringfy_term <- showTerm term
                              stringfy_type <- simpl type_ >>= showTerm
                              pushTypeError ("The destructed type must be a constructor instead of " ++ stringfy_type ++ " on " ++ stringfy_term ++ " where " ++ stringfy_match  ++ " is your jugdment") checker); -- The destructed type cannot be found
                   });
           _ -> return checker;
        }
  where
    generalize_constructor (App x y) = App x (Var (VarRef  "__"))
    generalize_constructor term = generalize_constructor ## term

checkTypeClauses :: Term -> ([Term], [Term]) -> Term -> Checker -> ContextM Checker
checkTypeClauses constr (constructors, predicates) helper checker = foldr (\term checkerM -> do
        checker <- checkerM
        checkClause checker term constr)
        (return checker) constructors
  where
    checkClause checker clause constr = do
       construction <- getConstructor clause
       case construction of {
          Just (Local name term (TermInfo Static _ _ _) ) ->
            foldTerm (\checkerM term -> do
            checker <- checkerM
            checkAgainstTypeConstructors term constr helper checker
            matchConstructorOptionalType checker name (predicates, helper) constr) (return checker) clause;
          _ -> do
           stringfy_constructor <- showTerm clause
           stringfy_constr <- showTerm constr
           pushTypeError ("Impossible of infer constructor" ++ stringfy_constructor ++ " in " ++ stringfy_constr ++ ", maybe it is not a constructor?") checker;
       }


constrRule :: Checker -> Term -> ContextM Checker
constrRule checker term = constr_typed term
  where
    constr_typed constr@(Constr type_ constructors) = do
            checker <- typeRules checker type_
            type_of_type <- getType type_
            case type_of_type of {
              Just x -> (do
                       setType (Jugdment constr x)
                       foldr (\constructor checkerM -> do
                                checker <- checkerM
                                checkAgainstTypeConstructors constructor type_ term checker
                        ) (return checker) constructors
                      );
              Nothing -> do
                      type_show <- showTerm type_
                      constr_show <- showTerm constr
                      pushTypeError ("Impossible of infer " ++ type_show ++ " on " ++ constr_show ++ " fail to construct the type constructor") checker
            }
    constr_typed _ = error "Internal Error : Constructor rule always must be applyed to a type constructor"


notationRule :: Checker -> Term-> ContextM Checker
notationRule checker notation@(Notation l@Lam{} type_) = do
        setType (Jugdment l type_)
        checker <- typeRules checker type_
        typeRules checker l

notationRule checker notation@(Notation body type_) = do
        uni <- getUnifier
        checker <- typeRules checker body
        clearUnifer
        checker <- typeRules checker type_
        checker <- assertType (Jugdment body type_) (Notation body type_) checker
        setType (Jugdment notation type_) --- why we need this? idk, but we need for sure!
        setType (Jugdment body type_)
        setUnifer uni
        return checker

notationRule _ _ = error "Internal Error : Notation rule always must be applyed to a notation term"


inferMatch:: Term -> ContextM ()
inferMatch match@(Match _ type_ _) = setType (Jugdment match type_)
inferMatch _ = error "Internal Error : Match inference always must be applyed to a match expression"

typeRules :: Checker -> Term -> ContextM Checker
typeRules checker term =
        case term of {
           lam@(Lam k t) -> (do
                   inferLambda lam -- insert type of k on the context of the body t 
                   checker <- typeRules checker k
                   checker <- typeRules checker t
                   absRule checker lam);
           var@(Var _) -> varRule checker var;
           app@(App x y) -> (do
                   checker <- typeRules checker x
                   checker <- typeRules checker y
                   appRule checker app
            );
           pi@(Pi var t t') -> (do
                   inferPi pi
                   checker <- typeRules checker t
                   checker <- typeRules checker t'
                   prodRule pi checker
           );
           match@(Match matched type_ body) -> (do
                   inferMatch match
                   checker <- typeRules checker matched
                   checker <- typeRules checker type_
                   unifier <- getUnifier
                   checker <- clauseChecker checker match (map fst body) matched
                   Prelude.foldr (\(predicate, term) checkerM -> do
                           checker <- checkerM
                           checker <- checkMatchBody matched type_ (predicate, term) checker
                           checker <- typeRules checker term
                           checker <- assertType (Jugdment term type_) match checker
                           setUnifer unifier
                           return checker
                           ) (return checker) body
            );
           constr@(Constr type' constructors) -> constrRule checker constr;
           Notation body type' -> do
                   type' <- normalize type'
                   notationRule checker (Notation body type');
        }

typeCheckerLocal :: ContextM Checker
typeCheckerLocal = do
        term <- getTerm
        typeRules (Checker{error_msg=[], hole_msg = []}) term

formatTypeChecker :: [(String, ([String], [String]))] -> String
formatTypeChecker r
  |not $ null r = do
          let format_msg x = foldr (\c str -> if c == '\n' then "\n  " ++ str else c : str) "" (" " ++ x)
          foldr (\(name, (erros, holes)) str -> do
                  let sep = if not $ null holes then "\n\n" else ""
                  "\nDefinition " ++ name ++ ":\n" ++ format_msg (first holes) ++ sep ++ format_msg (print_erros erros)) "" r
  |otherwise = "Kei checked your file with successful"
  where
    print_erros ls@(x : y : _) = x ++ "...\n\n" ++ last ls
    print_erros ls@(x : _) =  x
    print_erros _ = "\n"
    first (x : y) = x
    first [] = []

typeCheck :: [(String, Local)] -> String
typeCheck definitons = do
        let locals = map snd definitons
        let state = Definitions $ foldr (\local@(Local str _ _) y -> Map.insert str local y) Map.empty locals
        let k = check locals state
        let types_result = foldr (\(checker, name) ls -> do
                let erros = error_msg checker
                let holes = hole_msg checker
                if not (null erros) || not (null holes) then (name, (erros, holes)) : ls else ls) [] (fst k)
        formatTypeChecker types_result
  where
      check :: [Local] -> Definitions -> ([(Checker, String)], Definitions)
      check locals state =
        foldr (\local (checkers, state) -> do
                let (checker, Definitions map, l@(Local name _ (TermInfo sort _ t _))) = contextMrun typeCheckerLocal state local
                ((checker, name) : checkers, Definitions (Map.insert name l map))
        ) ([], state) locals