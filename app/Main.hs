module Main where
import System.Environment
import Parser
import Term
import Checker
import Data.Map (Map)
import qualified Data.Map as Map

main :: IO ()
main = do
    x <- getArgs
    case x of
        [x'] -> do
            n <- readFile (x' ++ ".kei")
            case Parser.run n of
                Right x_ -> do
                    let locals = state x_
                    putStrLn (typeCheck locals)
                Left y_ ->  print y_
        (x : xs) -> putStrLn "Error, there is no that option"
        [] -> putStrLn "Kei file don't found"