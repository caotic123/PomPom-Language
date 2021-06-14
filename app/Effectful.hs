module Effectful where
import System.Random
import Data.List ()

rand :: [Int]
rand = go $ mkStdGen 699494
    where 
        go gen = do 
            let (k, next) = uniformR (1 :: Int, 99999999) gen
            k : go next




