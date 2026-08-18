module Main where
import System.Environment
import Parser
import Term
import Debug.Trace
import Checker
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set

type FileDefinitions = [[(String, Local)]]

readKei :: String -> Set String -> IO (Maybe (Set String, FileDefinitions))
readKei file visited
  | Set.member file visited = return $ Just (visited, [])
  | otherwise = do
    source <- readFile (file ++ ".pom")
    case Parser.run source of
      Right (dependencies, definitions) -> do
        traceIO ("PomPom : cached " ++ file)
        loaded <- foldM loadImport (Just (Set.insert file visited, [])) dependencies
        case loaded of
          Just (records, imports) -> do
            traceIO ("PomPom : checking " ++ file ++ " ...")
            return $ Just (records, imports ++ [state definitions])
          Nothing -> return Nothing
      Left parseError -> do
        print parseError
        return Nothing
  where
    loadImport Nothing _ = return Nothing
    loadImport (Just (records, definitions)) dependency = do
      imported <- readKei dependency records
      return $ do
        (records', definitions') <- imported
        return (records', definitions ++ definitions')


main :: IO ()
main = do
    x <- getArgs
    case x of
        [x'] -> do
            read <- readKei x' Set.empty
            case read of {
              Just x -> putStrLn . typeCheck . concat . reverse $ snd x;
              Nothing -> putStrLn "PomPom : Error on executing file"
            }
        (x : xs) -> putStrLn "Error, there is no that option"
        [] -> putStrLn "Pompom file don't found"
