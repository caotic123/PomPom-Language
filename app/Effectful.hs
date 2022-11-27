module Effectful where
import System.Random
import Data.List ()
import Data.Time.Clock.System

rand :: [Int]
rand = genRand 699494 (1 :: Int, 99999999)

randIO :: (Int, Int) -> IO Int
randIO u = do
    time <- getSystemTime
    let (first, _) = uniformR u (mkStdGen (fromIntegral $ systemNanoseconds time))
    return first

genRand :: Int -> (Int, Int) -> [Int]
genRand x u = go $ mkStdGen x
    where 
        go gen = do 
            let (k, next) = uniformR u gen
            k : go next