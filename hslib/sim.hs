module Sim where

import Data.Array
import Data.Default
import Data.List(partition, foldl')
import Data.Colour
import System.Random
import qualified Diagrams.Prelude as D
import Diagrams.TwoD.Layout.Tree
import Physics.ForceLayout
import CartesianTree
import Vis
import CT

request  :: RandomGen g => Int -> Int -> g -> [Int]
request min max = randomRs (min, max)
duration :: RandomGen g => g -> [Int]
duration = map (values !) . randomRs (1,size)
  where 
    durations = [(64,1), (32,5), (16,10), (8,20), (4,30), (2,50),(1,100),(1,256),(1,512),(1,1024)]
    size      = sum (map fst durations)
    values :: Array Int Int
    values = listArray (1,size) (concatMap (uncurry replicate) durations)

type Piece  = ((Int,Int),Int) -- ((address, length), duration)
type PQueue = PQ Piece  

step :: (Int,Int)  -- (request, duration)
     -> (Heap, PQueue)  -- current heap
     -> (Heap, PQueue)
step (request, duration) (heap, queue)
  = let (expired, queue') = popWhilePQ (==0) $ mapPQ (subtract 1) queue
        freed_heap = foldl' free heap expired
    in case allocate freed_heap request of
         Left heap'           -> (heap', queue')
         Right (piece, heap') -> (heap', pushPQ (piece, duration) queue')

type PQ a = [a]
emptyPQ = []
mapPQ f = map (\ (block, duration) -> (block, f duration))
popWhilePQ p q = let (expired, next) = partition (p . snd) q
                 in (map fst expired, next)
pushPQ  = (:)                 

free :: Heap -> (Int, Int) -> Heap
free h p     = fst3 $ runVis (istate,iconfig) $
                 fmap close (attach undefined p (zipper h) >>= promote)
allocate :: Heap -> Int -> Either Heap ((Int,Int), Heap)
allocate h l = fst3 $ runVis (istate,iconfig) $
                 delete l h

fst3 (a, _, _) = a

simulate sz = fmap strip . fst . foldl' (flip step) (initial sz, emptyPQ)
  where
    initial sz = Node (defaultV { _addr = 0, _len = sz }) Leaf Leaf
    defaultV = V undefined undefined
                 undefined undefined
                 undefined
                 undefined undefined
    strip (V _ _ _ _ _ a l) = (a,l)

simulate' sz reqs = let trace = go ((initial sz, emptyPQ), reqs) []
                        size  = length trace
                        gap   = (size `div` 50) `max` 1
                        trace' = groupBy 5 $ map (render . head) $ take 50 $ iterate (drop gap) trace
                    in D.vcat' def{ D.sep = 1} (map (D.hcat' def{ D.sep = 0.3 }) trace')
  where
    initial sz = Node (defaultV { _addr = 0, _len = sz }) Leaf Leaf
    defaultV = V undefined undefined
                 undefined undefined
                 undefined
                 undefined undefined

    groupBy cnt []   = []
    groupBy cnt list = let (s,r) = splitAt cnt list in s:groupBy cnt r

    go (_, []) heaps = heaps
    go (heapAndQueue, r:reqs) out = let hq@(h, _) = step r heapAndQueue
                                    in go (hq, reqs) (iso h:out)
      where
        iso (Node (V _ _ _ _ _ addr len) l r) = BNode (addr,len) (iso l) (iso r)
        iso Leaf                         = Empty

    render t = let Just t' = uniqueXLayout 1 1 t
                   tree    = renderTree (\n -> (D.text (show n) D.# D.fontSize 0.5)             D.<> 
                                               (D.circle 0.3) D.# D.fc D.white D.# D.lc D.white D.<>
                                               (D.rect 5 0.6 D.# D.fcA transparent D.# D.lc D.white))
                                        (D.~~)
                                        (forceLayoutTree' def{forceLayoutOpts = FLOpts { damping     = 0.8
                                                                                        , energyLimit = Just 0.001
                                                                                        , stepLimit   = Just 50
                                                                                        }} t')
                   (w,h)   = D.size2D tree
               in    D.alignT (D.rect w h) `D.atop` D.alignT     tree
                  

