module Main where
import System.Environment
import Parser
import Term
import Debug.Trace
import Checker
import Control.Monad
import Data.Set hiding (map, foldr)
import Data.Functor

readKei :: String -> Set String -> IO (Maybe (Set String, [(String, Local)]))
readKei file set = do
    n <- readFile (file ++ ".pom")
    case Parser.run n of
      Right x_ -> do
        trace ("PomPom : cached " ++ file) return ()
        rec_ <- foldM (\x y -> mapM (\x -> readKei y (fst x) <&> foldDefs (Just x)) x <&> join) (pure (Data.Set.empty, [])) (fst x_)
        return $ do
          (records, imports) <- rec_
          let u_set = Data.Set.union set records
          if Data.Set.member file set then
              return (u_set, imports)
             else do
              trace ("PomPom : checking " ++ file ++ " ...") return (Data.Set.insert file u_set, state (snd x_) ++ imports)
      Left y_ -> do
          print y_
          return Nothing
  where
    foldDefs m m' = do
        (set, ls) <- m
        (set', ls') <- m'
        return (Data.Set.union set set', ls ++ ls')


main :: IO ()
main = do
    x <- getArgs
    case x of
        [x'] -> do
            read <- readKei x' Data.Set.empty
            case read of {
              Just x -> putStrLn . typeCheck $ snd x;
              Nothing -> putStrLn "PomPom : Error on executing file"
            }
        (x : xs) -> putStrLn "Error, there is no that option"
        [] -> putStrLn "Pompom file don't found"