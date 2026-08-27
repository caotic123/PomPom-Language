module Main where

import Control.Monad (foldM)
import Data.List (foldl')
import Data.Map (Map)
import Data.Set (Set)
import System.Environment (getArgs)
import Text.Read (readMaybe)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Parser
import qualified Term

data Expected = ExpectAccept | ExpectReject deriving (Eq, Show)

data Selection
  = SelectAll
  | SelectSlice Int Int
  | SelectCurrent
  | SelectCurrentSlice Int Int
  deriving (Eq, Show)

data Loaded = Loaded
  { loadedVisited :: Set String
  , loadedGroups :: [[Term.Local]]
  , loadedDuplicatePatternBinder :: Bool
  }

data Encoding = Encoding
  { encodedReferences :: Map String Int
  , encodedBoundVariables :: Map Int Int
  }

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    [entrypoint, output, expectedText] -> generate entrypoint output expectedText SelectAll
    [entrypoint, output, expectedText, "current"] -> generate entrypoint output expectedText SelectCurrent
    [entrypoint, output, expectedText, limitText] -> case readMaybe limitText of
      Just limit | limit >= 0 -> generate entrypoint output expectedText (SelectSlice 0 limit)
      _ -> fail "declaration limit must be a non-negative integer"
    [entrypoint, output, expectedText, offsetText, limitText] -> case (readMaybe offsetText, readMaybe limitText) of
      (Just offset, Just limit) | offset >= 0 && limit >= 0 -> generate entrypoint output expectedText (SelectSlice offset limit)
      _ -> fail "declaration offset and limit must be non-negative integers"
    [entrypoint, output, expectedText, "current", offsetText, limitText] -> case (readMaybe offsetText, readMaybe limitText) of
      (Just offset, Just limit) | offset >= 0 && limit >= 0 -> generate entrypoint output expectedText (SelectCurrentSlice offset limit)
      _ -> fail "current declaration offset and limit must be non-negative integers"
    _ -> fail "usage: KeiBootstrap ENTRYPOINT OUTPUT (accept|reject) [current [OFFSET DECLARATION_LIMIT] | DECLARATION_LIMIT | OFFSET DECLARATION_LIMIT]"

generate :: String -> FilePath -> String -> Selection -> IO ()
generate entrypoint output expectedText selection = do
      expected <- case expectedText of
        "accept" -> pure ExpectAccept
        "reject" -> pure ExpectReject
        _ -> fail "expected verdict must be 'accept' or 'reject'"
      loaded <- loadPomPom entrypoint (Loaded Set.empty [] False)
      let (inputExpression, pendingExpression, bridgeClassification, currentCount, pendingCount) = case loaded of
            Left _ -> ("bootstrap-parse-error-input", Nothing, "parse-error", 0, 0)
            Right result
              | loadedDuplicatePatternBinder result -> ("bootstrap-parse-error-input", Nothing, "repeated-pattern-binder", 0, 0)
              | otherwise ->
                  let allLocals = concat (reverse (loadedGroups result))
                      checkOrder = reverse allLocals
                      currentLocals = case reverse (loadedGroups result) of
                        current : _ -> reverse current
                        [] -> []
                      locals = case selection of
                        SelectAll -> checkOrder
                        SelectSlice offset limit -> take limit (drop offset checkOrder)
                        SelectCurrent -> currentLocals
                        SelectCurrentSlice offset limit -> take limit (drop offset currentLocals)
                      encoding = buildEncoding allLocals
                      allBindings = encodeBindings encoding allLocals
                      pendingBindings = encodeBindings encoding locals
                      certificates = encodeCertificates encoding (generateCertificates allLocals locals)
                  in ("(bootstrap-program-input " ++ allBindings ++ ")", Just (allBindings, pendingBindings, certificates), "parsed", length currentLocals, length locals)
          source = case pendingExpression of
            Nothing -> renderHarness inputExpression expected
            Just (allBindings, pendingBindings, certificates) -> renderProgramHarness allBindings pendingBindings certificates expected
      writeFile output source
      putStrLn ("Bootstrap harness written to " ++ output)
      putStrLn ("Bootstrap bridge classification: " ++ bridgeClassification)
      putStrLn ("Bootstrap current declarations: " ++ show currentCount)
      putStrLn ("Bootstrap pending declarations: " ++ show pendingCount)

loadPomPom :: String -> Loaded -> IO (Either String Loaded)
loadPomPom entrypoint loaded
  | Set.member entrypoint (loadedVisited loaded) = pure (Right loaded)
  | otherwise = do
      source <- readFile (entrypoint ++ ".pom")
      case Parser.run source of
        Left parseError -> pure (Left (show parseError))
        Right (dependencies, definitions) -> do
          let visited = Set.insert entrypoint (loadedVisited loaded)
              duplicate = any (definitionHasDuplicatePatternBinder . third) definitions
              seeded = loaded
                { loadedVisited = visited
                , loadedDuplicatePatternBinder = loadedDuplicatePatternBinder loaded || duplicate
                }
          imported <- foldM loadDependency (Right seeded) dependencies
          pure $ do
            importedState <- imported
            let locals = map snd (Term.state definitions)
            pure importedState {loadedGroups = loadedGroups importedState ++ [locals]}
  where
    loadDependency (Left problem) _ = pure (Left problem)
    loadDependency (Right current) dependency = loadPomPom dependency current

    third (_, _, value) = value

definitionHasDuplicatePatternBinder :: Parser.PTerm -> Bool
definitionHasDuplicatePatternBinder parsed = case parsed of
  Parser.PType _ domain body -> go domain || go body
  Parser.PLam _ body annotation -> go body || maybe False go annotation
  Parser.PApp function argument -> go function || go argument
  Parser.PVar _ -> False
  Parser.PMatch scrutinee result clauses ->
    go scrutinee || go result || any clauseProblem clauses
  Parser.PConstructors family constructors -> go family || any go constructors
  Parser.PTatic terms -> any go terms
  Parser.PNotation body annotation -> go body || go annotation
  Parser.PDef _ value body -> go value || go body
  where
    go = definitionHasDuplicatePatternBinder
    clauseProblem (patternTerm, body) = duplicatePatternArguments patternTerm || go patternTerm || go body

duplicatePatternArguments :: Parser.PTerm -> Bool
duplicatePatternArguments patternTerm =
  let (_, arguments) = flattenApplication patternTerm
      names = [name | Parser.PVar name <- arguments, name /= "_"]
  in length names /= Set.size (Set.fromList names)
  where
    flattenApplication term = case term of
      Parser.PApp function argument ->
        let (root, arguments) = flattenApplication function
        in (root, arguments ++ [argument])
      _ -> (term, [])

renderHarness :: String -> Expected -> String
renderHarness inputExpression expected = unlines
  [ "import boostrap/driver."
  , ""
  , "bootstrap-generated-input"
  , "  " ++ inputExpression ++ "."
  , ""
  , "bootstrap-generated-certificates"
  , "  (empty BootstrapNormalizationCertificate)."
  , ""
  , "bootstrap-generated-proof"
  , "  ((refl Bool " ++ expectedBool ++ ") :: (Eq Bool (bootstrap-verdict-is-accept (bootstrap-check-input-recur (bootstrap-input-check-work-new bootstrap-generated-input bootstrap-generated-certificates))) " ++ expectedBool ++ "))."
  ]
  where
    expectedBool = case expected of
      ExpectAccept -> "true"
      ExpectReject -> "false"

renderProgramHarness :: String -> String -> String -> Expected -> String
renderProgramHarness allBindings pendingBindings certificates expected = unlines
  [ "import boostrap/driver."
  , ""
  , "bootstrap-generated-bindings"
  , "  " ++ allBindings ++ "."
  , ""
  , "bootstrap-generated-pending"
  , "  " ++ pendingBindings ++ "."
  , ""
  , "bootstrap-generated-certificates"
  , "  " ++ certificates ++ "."
  , ""
  , "bootstrap-generated-proof"
  , "  ((refl Bool " ++ expectedBool ++ ") :: (Eq Bool (bootstrap-driver-output-succeeded (bootstrap-driver-recur (bootstrap-driver-work-new bootstrap-generated-pending (bootstrap-empty-environment bootstrap-generated-bindings bootstrap-generated-certificates) (bootstrap-binding-list-accessibility-instance bootstrap-generated-pending)))) " ++ expectedBool ++ "))."
  ]
  where
    expectedBool = case expected of
      ExpectAccept -> "true"
      ExpectReject -> "false"

encodeBindings :: Encoding -> [Term.Local] -> String
encodeBindings encoding locals = pomList "BootstrapBinding" (encodeLocal encoding) locals

encodeCertificates :: Encoding -> [(Term.Term, [Term.Term])] -> String
encodeCertificates encoding = pomList "BootstrapNormalizationCertificate" encodeCertificate
  where
    encodeCertificate (start, path) =
      "(bootstrap-normalization-certificate-new "
        ++ maybe "\"\"" (encodeReference encoding) (termRootReference start) ++ " "
        ++ encodeTerm encoding start ++ " "
        ++ pomList "BootstrapTerm" (encodeTerm encoding) path
        ++ ")"

generateCertificates :: [Term.Local] -> [Term.Local] -> [(Term.Term, [Term.Term])]
generateCertificates environmentLocals candidateLocals = Map.toList (foldl' addCandidate Map.empty candidates)
  where
    bindings = foldr insertBinding Map.empty environmentLocals
    insertBinding local@(Term.Local name _ _) = Map.insert name local
    candidates = uniqueTerms (concatMap (localTypeCandidates bindings) candidateLocals)

    addCandidate certificates candidate = case normalizationPath bindings candidate of
      Nothing -> certificates
      Just [] -> certificates
      Just path -> Map.insertWith keepExisting candidate path certificates

    keepExisting _ existing = existing

termRootReference :: Term.Term -> Maybe String
termRootReference term = case term of
  Term.Var (Term.VarRef name) -> Just name
  Term.Var (Term.VarName _) -> Nothing
  Term.App function _ -> termRootReference function
  Term.Constr family _ -> termRootReference family
  Term.Notation body _ -> termRootReference body
  Term.Pi _ _ _ -> Nothing
  Term.Lam _ _ -> Nothing
  Term.Match _ _ _ -> Nothing

localTypeCandidates :: Map String Term.Local -> Term.Local -> [Term.Term]
localTypeCandidates bindings (Term.Local _ body info) =
  let contextCandidates = concatMap (\(key, value) -> allSubterms key ++ allSubterms value) (Map.toList (Term.context info))
      rootCandidates = case Term.sort info of
        Term.Static -> allSubterms body
        Term.Expression -> discoverTypePositions body
      inferredCandidates = discoverTypingCandidates bindings (Term.context info) Nothing body
  in rootCandidates ++ contextCandidates ++ inferredCandidates

discoverTypingCandidates :: Map String Term.Local -> Map Term.Term Term.Term -> Maybe Term.Term -> Term.Term -> [Term.Term]
discoverTypingCandidates bindings context expected term =
  maybe [] (: []) expected
    ++ maybe [] (: []) (inferKnownType bindings context Set.empty term)
    ++ case term of
      Term.Var _ -> []
      Term.Pi binder domain body ->
        discoverTypingCandidates bindings context Nothing domain
          ++ discoverTypingCandidates bindings (Map.insert binder domain context) Nothing body
      Term.Lam binder body -> case expected >>= normalizeKnown bindings of
        Just normalizedExpected -> case eraseHostAnnotations normalizedExpected of
          Term.Pi expectedBinder domain codomain ->
            let renamedCodomain = substituteTerm expectedBinder binder codomain
                bodyContext = Map.insert binder domain context
            in renamedCodomain : discoverTypingCandidates bindings bodyContext (Just renamedCodomain) body
          _ -> discoverTypingCandidates bindings context Nothing body
        Nothing -> discoverTypingCandidates bindings context Nothing body
      Term.App function argument ->
        discoverTypingCandidates bindings context Nothing function
          ++ discoverTypingCandidates bindings context Nothing argument
      Term.Constr family constructors ->
        discoverTypingCandidates bindings context Nothing family
          ++ concatMap (discoverTypingCandidates bindings context Nothing) constructors
      Term.Match scrutinee result clauses ->
        let scrutineeType = inferKnownType bindings context Set.empty scrutinee
            branchCandidates (patternTerm, body) =
              let instantiatedResult = substituteTerm scrutinee patternTerm result
              in instantiatedResult
                  : discoverTypingCandidates bindings context scrutineeType patternTerm
                    ++ discoverTypingCandidates bindings context (Just instantiatedResult) body
        in discoverTypingCandidates bindings context Nothing scrutinee
            ++ discoverTypingCandidates bindings context Nothing result
            ++ concatMap branchCandidates clauses
      Term.Notation body annotation ->
        annotation
          : discoverTypingCandidates bindings context Nothing annotation
            ++ discoverTypingCandidates bindings context (Just annotation) body

inferKnownType :: Map String Term.Local -> Map Term.Term Term.Term -> Set String -> Term.Term -> Maybe Term.Term
inferKnownType bindings context visiting term = case Map.lookup term context of
  Just known -> Just known
  Nothing -> case term of
    Term.Var (Term.VarName _) -> Nothing
    Term.Var (Term.VarRef name)
      | name == "*" -> Just (Term.Var (Term.VarRef "Type"))
      | name == "Type" -> Just (Term.Var (Term.VarRef "Kind"))
      | Set.member name visiting -> Nothing
      | otherwise -> case Map.lookup name bindings of
          Nothing -> Nothing
          Just (Term.Local _ body info) -> case Term.sort info of
            Term.Static -> Just body
            Term.Expression -> case body of
              Term.Notation _ annotation -> Just annotation
              Term.Constr family _ -> inferKnownType bindings context (Set.insert name visiting) family
              _ -> Nothing
    Term.Pi _ _ _ -> Just (Term.Var (Term.VarRef "Type"))
    Term.Lam _ _ -> Nothing
    Term.App function argument -> do
      functionType <- inferKnownType bindings context visiting function
      normalizedFunctionType <- normalizeKnown bindings functionType
      case eraseHostAnnotations normalizedFunctionType of
        Term.Pi binder _ codomain -> Just (substituteTerm binder argument codomain)
        _ -> Nothing
    Term.Constr family _ -> inferKnownType bindings context visiting family
    Term.Match _ result _ -> Just result
    Term.Notation _ annotation -> Just annotation

normalizeKnown :: Map String Term.Local -> Term.Term -> Maybe Term.Term
normalizeKnown bindings term = case normalizationPath bindings term of
  Nothing -> Nothing
  Just [] -> Just term
  Just path -> Just (last path)

eraseHostAnnotations :: Term.Term -> Term.Term
eraseHostAnnotations term = case term of
  Term.Var _ -> term
  Term.Pi binder domain body -> Term.Pi binder (eraseHostAnnotations domain) (eraseHostAnnotations body)
  Term.Lam binder body -> Term.Lam binder (eraseHostAnnotations body)
  Term.App function argument -> Term.App (eraseHostAnnotations function) (eraseHostAnnotations argument)
  Term.Constr family constructors -> Term.Constr (eraseHostAnnotations family) (map eraseHostAnnotations constructors)
  Term.Match scrutinee result clauses ->
    Term.Match
      (eraseHostAnnotations scrutinee)
      (eraseHostAnnotations result)
      [(eraseHostAnnotations patternTerm, eraseHostAnnotations body) | (patternTerm, body) <- clauses]
  Term.Notation body _ -> eraseHostAnnotations body

discoverTypePositions :: Term.Term -> [Term.Term]
discoverTypePositions term = case term of
  Term.Var _ -> []
  Term.Pi _ domain body -> allSubterms domain ++ allSubterms body
  Term.Lam _ body -> discoverTypePositions body
  Term.App function argument -> discoverTypePositions function ++ discoverTypePositions argument
  Term.Constr family constructors -> allSubterms family ++ concatMap discoverTypePositions constructors
  Term.Match scrutinee result clauses ->
    allSubterms result
      ++ concatMap (\(patternTerm, _) -> allSubterms (substituteTerm scrutinee patternTerm result)) clauses
      ++ discoverTypePositions scrutinee
      ++ concatMap (\(patternTerm, body) -> discoverTypePositions patternTerm ++ discoverTypePositions body) clauses
  Term.Notation body annotation -> allSubterms annotation ++ discoverTypePositions body

allSubterms :: Term.Term -> [Term.Term]
allSubterms term = term : case term of
  Term.Var _ -> []
  Term.Pi binder domain body -> allSubterms binder ++ allSubterms domain ++ allSubterms body
  Term.Lam binder body -> allSubterms binder ++ allSubterms body
  Term.App function argument -> allSubterms function ++ allSubterms argument
  Term.Constr family constructors -> allSubterms family ++ concatMap allSubterms constructors
  Term.Match scrutinee result clauses ->
    allSubterms scrutinee ++ allSubterms result ++ concatMap (\(patternTerm, body) -> allSubterms patternTerm ++ allSubterms body) clauses
  Term.Notation body annotation -> allSubterms body ++ allSubterms annotation

uniqueTerms :: [Term.Term] -> [Term.Term]
uniqueTerms = reverse . snd . foldl' insertFresh (Set.empty, [])
  where
    insertFresh (seen, ordered) term
      | Set.member term seen = (seen, ordered)
      | otherwise = (Set.insert term seen, term : ordered)

data ReductionStep = ReductionNormal | ReductionReduced Term.Term

normalizationPath :: Map String Term.Local -> Term.Term -> Maybe [Term.Term]
normalizationPath bindings start = walk (Set.singleton start) start
  where
    walk visited current = case reduceOnce bindings current of
      ReductionNormal -> Just []
      ReductionReduced next
        | Set.member next visited -> Nothing
        | otherwise -> (next :) <$> walk (Set.insert next visited) next

reduceOnce :: Map String Term.Local -> Term.Term -> ReductionStep
reduceOnce bindings term = case term of
  Term.Var (Term.VarName _) -> ReductionNormal
  Term.Var (Term.VarRef name) -> case Map.lookup name bindings of
    Just (Term.Local _ body info) -> case Term.sort info of
      Term.Expression -> ReductionReduced body
      Term.Static -> ReductionNormal
    _ -> ReductionNormal
  Term.Pi binder domain body -> case reduceOnce bindings domain of
    ReductionReduced newDomain -> ReductionReduced (Term.Pi binder newDomain body)
    ReductionNormal -> case reduceOnce bindings body of
      ReductionReduced newBody -> ReductionReduced (Term.Pi binder domain newBody)
      ReductionNormal -> ReductionNormal
  Term.Lam binder body -> case reduceOnce bindings body of
    ReductionReduced newBody -> ReductionReduced (Term.Lam binder newBody)
    ReductionNormal -> ReductionNormal
  Term.App (Term.Notation body _) argument -> ReductionReduced (Term.App body argument)
  Term.App (Term.Lam binder body) argument -> ReductionReduced (substituteTerm binder argument body)
  Term.App function argument -> case reduceOnce bindings function of
    ReductionReduced newFunction -> ReductionReduced (Term.App newFunction argument)
    ReductionNormal -> case reduceOnce bindings argument of
      ReductionReduced newArgument -> ReductionReduced (Term.App function newArgument)
      ReductionNormal -> ReductionNormal
  Term.Constr family constructors -> case reduceOnce bindings family of
    ReductionReduced newFamily -> ReductionReduced (Term.Constr newFamily constructors)
    ReductionNormal -> ReductionNormal
  Term.Match (Term.Notation scrutinee _) result clauses -> ReductionReduced (Term.Match scrutinee result clauses)
  Term.Match scrutinee result clauses -> case scrutinee of
    Term.Var _ -> case reduceOnce bindings scrutinee of
      ReductionReduced newScrutinee -> ReductionReduced (Term.Match newScrutinee result clauses)
      ReductionNormal -> case reduceOnce bindings result of
        ReductionReduced newResult -> ReductionReduced (Term.Match scrutinee newResult clauses)
        ReductionNormal -> maybe ReductionNormal ReductionReduced (selectClause scrutinee clauses)
    Term.App _ _ -> case reduceOnce bindings scrutinee of
      ReductionReduced newScrutinee -> ReductionReduced (Term.Match newScrutinee result clauses)
      ReductionNormal -> maybe ReductionNormal ReductionReduced (selectClause scrutinee clauses)
    Term.Constr _ _ -> maybe ReductionNormal ReductionReduced (selectClause scrutinee clauses)
    Term.Pi _ _ _ -> reduceMatchScrutineeOnly
    Term.Lam _ _ -> reduceMatchScrutineeOnly
    Term.Match _ _ _ -> reduceMatchScrutineeOnly
    where
      reduceMatchScrutineeOnly = case reduceOnce bindings scrutinee of
        ReductionReduced newScrutinee -> ReductionReduced (Term.Match newScrutinee result clauses)
        ReductionNormal -> ReductionNormal
  Term.Notation _ _ -> ReductionNormal

substituteTerm :: Term.Term -> Term.Term -> Term.Term -> Term.Term
substituteTerm target replacement term
  | term == target = replacement
  | otherwise = case term of
      Term.Var _ -> term
      Term.Pi binder domain body -> Term.Pi binder (substituteTerm target replacement domain) (substituteTerm target replacement body)
      Term.Lam binder body
        | binder == target -> term
        | otherwise -> Term.Lam binder (substituteTerm target replacement body)
      Term.App function argument -> Term.App (substituteTerm target replacement function) (substituteTerm target replacement argument)
      Term.Constr family constructors -> Term.Constr (substituteTerm target replacement family) (map (substituteTerm target replacement) constructors)
      Term.Match scrutinee result clauses ->
        Term.Match
          (substituteTerm target replacement scrutinee)
          (substituteTerm target replacement result)
          [(patternTerm, substituteTerm target replacement body) | (patternTerm, body) <- clauses]
      Term.Notation body annotation -> Term.Notation (substituteTerm target replacement body) (substituteTerm target replacement annotation)

patternMatches :: Term.Term -> Term.Term -> Bool
patternMatches patternTerm scrutinee = case patternTerm of
  Term.Var (Term.VarName _) -> True
  Term.Var (Term.VarRef name) -> scrutinee == Term.Var (Term.VarRef name)
  Term.App patternFunction patternArgument -> case scrutinee of
    Term.App scrutineeFunction scrutineeArgument ->
      patternMatches patternFunction scrutineeFunction && patternMatches patternArgument scrutineeArgument
    _ -> False
  _ -> False

destructPattern :: Term.Term -> Term.Term -> Term.Term -> Maybe Term.Term
destructPattern patternTerm scrutinee body = case patternTerm of
  variable@(Term.Var (Term.VarName _)) -> Just (substituteTerm variable scrutinee body)
  Term.Var (Term.VarRef _) -> Just body
  Term.App patternFunction patternArgument -> case scrutinee of
    Term.App scrutineeFunction scrutineeArgument -> do
      argumentBody <- destructPattern patternArgument scrutineeArgument body
      destructPattern patternFunction scrutineeFunction argumentBody
    _ -> Nothing
  _ -> Just body

selectClause :: Term.Term -> [(Term.Term, Term.Term)] -> Maybe Term.Term
selectClause scrutinee clauses = choose (reverse clauses)
  where
    choose [] = Nothing
    choose ((patternTerm, body) : rest)
      | patternMatches patternTerm scrutinee = destructPattern patternTerm scrutinee body
      | otherwise = choose rest

encodeLocal :: Encoding -> Term.Local -> String
encodeLocal encoding (Term.Local name body info) =
  let contextEntries = Map.toList (Term.context info)
  in "(bootstrap-binding-new "
      ++ encodeReference encoding name ++ " "
      ++ encodeSort (Term.sort info) ++ " "
      ++ encodeTerm encoding body ++ " "
      ++ pomList "BootstrapTyping" (encodeTyping encoding) contextEntries
      ++ ")"

encodeSort :: Term.Sort -> String
encodeSort sort = case sort of
  Term.Static -> "bootstrap-static-sort"
  Term.Expression -> "bootstrap-expression-sort"

encodeTyping :: Encoding -> (Term.Term, Term.Term) -> String
encodeTyping encoding (key, value) =
  "(bootstrap-typing-new " ++ encodeTerm encoding key ++ " " ++ encodeTerm encoding value ++ ")"

encodeTerm :: Encoding -> Term.Term -> String
encodeTerm encoding term = case term of
  Term.Var variable -> "(bootstrap-variable-term " ++ encodeVariable encoding variable ++ ")"
  Term.Pi binder domain body ->
    "(bootstrap-pi-term " ++ encodeBinder encoding binder ++ " " ++ encodeTerm encoding domain ++ " " ++ encodeTerm encoding body ++ ")"
  Term.Lam binder body ->
    "(bootstrap-lambda-term " ++ encodeBinder encoding binder ++ " " ++ encodeTerm encoding body ++ ")"
  Term.App function argument ->
    "(bootstrap-application-term " ++ encodeTerm encoding function ++ " " ++ encodeTerm encoding argument ++ ")"
  Term.Constr family constructors ->
    "(bootstrap-constructors-term " ++ encodeTerm encoding family ++ " " ++ pomList "BootstrapTerm" (encodeTerm encoding) constructors ++ ")"
  Term.Match scrutinee result clauses ->
    "(bootstrap-match-term " ++ encodeTerm encoding scrutinee ++ " " ++ encodeTerm encoding result ++ " " ++ pomList "BootstrapClause" (encodeClause encoding) clauses ++ ")"
  Term.Notation body annotation ->
    "(bootstrap-notation-term " ++ encodeTerm encoding body ++ " " ++ encodeTerm encoding annotation ++ ")"

encodeClause :: Encoding -> (Term.Term, Term.Term) -> String
encodeClause encoding (patternTerm, body) =
  "(bootstrap-clause-new " ++ encodeTerm encoding patternTerm ++ " " ++ encodeTerm encoding body ++ ")"

encodeBinder :: Encoding -> Term.Term -> String
encodeBinder encoding binder = case binder of
  Term.Var variable -> encodeVariable encoding variable
  _ -> error "purified Pi/lambda binder was not a variable"

encodeVariable :: Encoding -> Term.VarName -> String
encodeVariable encoding variable = case variable of
  Term.VarName identifier -> "(bootstrap-bound-name-var " ++ encodeBoundVariable encoding identifier ++ ")"
  Term.VarRef name -> "(bootstrap-reference-var " ++ encodeReference encoding name ++ ")"

encodeReference :: Encoding -> String -> String
encodeReference encoding name = case name of
  "*" -> show "2a"
  "Type" -> show "54797065"
  "Kind" -> show "4b696e64"
  "__" -> show "5f5f"
  "_" -> show "5f"
  _ -> case Map.lookup name (encodedReferences encoding) of
    Just identifier -> show ("r" ++ show identifier)
    Nothing -> error ("reference missing from bootstrap encoding: " ++ name)

encodeBoundVariable :: Encoding -> Int -> String
encodeBoundVariable encoding identifier = case Map.lookup identifier (encodedBoundVariables encoding) of
  Just denseIdentifier -> show ("b" ++ show denseIdentifier)
  Nothing -> error ("bound variable missing from bootstrap encoding: " ++ show identifier)

buildEncoding :: [Term.Local] -> Encoding
buildEncoding locals = Encoding referenceMap boundMap
  where
    references = Set.toAscList (Set.fromList (concatMap collectLocalReferences locals))
    boundVariables = Set.toAscList (Set.fromList (concatMap collectLocalBoundVariables locals))
    referenceMap = Map.fromList (zip references [0 ..])
    boundMap = Map.fromList (zip boundVariables [0 ..])

collectLocalReferences :: Term.Local -> [String]
collectLocalReferences (Term.Local name body info) =
  name : concatMap collectTermReferences (body : contextTerms)
  where
    contextTerms = concatMap (\(key, value) -> [key, value]) (Map.toList (Term.context info))

collectTermReferences :: Term.Term -> [String]
collectTermReferences term = case term of
  Term.Var (Term.VarRef name) -> [name]
  Term.Var (Term.VarName _) -> []
  Term.Pi binder domain body -> collectTermReferences binder ++ collectTermReferences domain ++ collectTermReferences body
  Term.Lam binder body -> collectTermReferences binder ++ collectTermReferences body
  Term.App function argument -> collectTermReferences function ++ collectTermReferences argument
  Term.Constr family constructors -> collectTermReferences family ++ concatMap collectTermReferences constructors
  Term.Match scrutinee result clauses ->
    collectTermReferences scrutinee ++ collectTermReferences result ++ concatMap (\(patternTerm, body) -> collectTermReferences patternTerm ++ collectTermReferences body) clauses
  Term.Notation body annotation -> collectTermReferences body ++ collectTermReferences annotation

collectLocalBoundVariables :: Term.Local -> [Int]
collectLocalBoundVariables (Term.Local _ body info) = collectLocalIdentifiers body info

collectLocalIdentifiers :: Term.Term -> Term.TermInfo -> [Int]
collectLocalIdentifiers body info =
  let contextTerms = concatMap (\(key, value) -> [key, value]) (Map.toList (Term.context info))
      identifiers = concatMap collectTermIdentifiers (body : contextTerms)
  in reverse (snd (foldl' insertFresh (Set.empty, []) identifiers))
  where
    insertFresh (seen, ordered) identifier
      | Set.member identifier seen = (seen, ordered)
      | otherwise = (Set.insert identifier seen, identifier : ordered)

collectTermIdentifiers :: Term.Term -> [Int]
collectTermIdentifiers term = case term of
  Term.Var (Term.VarName identifier) -> [identifier]
  Term.Var (Term.VarRef _) -> []
  Term.Pi binder domain body -> collectTermIdentifiers binder ++ collectTermIdentifiers domain ++ collectTermIdentifiers body
  Term.Lam binder body -> collectTermIdentifiers binder ++ collectTermIdentifiers body
  Term.App function argument -> collectTermIdentifiers function ++ collectTermIdentifiers argument
  Term.Constr family constructors -> collectTermIdentifiers family ++ concatMap collectTermIdentifiers constructors
  Term.Match scrutinee result clauses ->
    collectTermIdentifiers scrutinee ++ collectTermIdentifiers result ++ concatMap (\(patternTerm, body) -> collectTermIdentifiers patternTerm ++ collectTermIdentifiers body) clauses
  Term.Notation body annotation -> collectTermIdentifiers body ++ collectTermIdentifiers annotation

pomList :: String -> (a -> String) -> [a] -> String
pomList typeName encode = foldr step ("(empty " ++ typeName ++ ")")
  where
    step value rest = "(new " ++ typeName ++ " " ++ encode value ++ " " ++ rest ++ ")"
