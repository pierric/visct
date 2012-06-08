module Main where

{--
import System.Random
import CartesianTree
import Sim

main = do
  (g1,g2) <- fmap split getStdGen
  let reqs = take 30000 $ zip (request 8 1000 g1) (duration g2)
  let tree = simulate 1000000 reqs
  putStrLn $ "Depth: " ++ (show $ depth tree) ++ " ;Size: " ++ (show $ size tree)
  putStrLn $ show tree
--}

import Diagrams.Backend.Cairo.CmdLine
import System.Random
import Sim

main = do 
  (g1,g2) <- fmap split getStdGen
  let !reqs = take 1000 $ zip (request 8 1000 g1) (duration g2)
  defaultMain (simulate' 1000000 reqs)

