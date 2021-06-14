module Main where
import System.Environment
import Parser
import Term

import Data.Map (Map)
import qualified Data.Map as Map

main :: IO ()
main = do
    x <- getArgs
    case x of
        [x'] -> do
            n <- readFile (x' ++ ".kei")
            case run n of
                Right x_ -> do
                    let (k, terminf) = unzip $ map (\(def_name, term) -> transform term) x_
                    print k
                    --print (map (Map.toList . var_names) terminf)
                Left y_ ->  print y_
        (x : xs) -> putStrLn "Error, there is no that option"
        [] -> putStrLn "Kei file don't found"