{- Defined the CartesianTree structure, its navigation type Zipper,
 - and navigation operation on Zipper
 -}
module CartesianTree (
  CartesianTree(..),
  Zipper,
  zipper,
  left, leftJust,
  right, rightJust,
  up, upJust,
  root,
  isRoot, isLeaf,
  viewf, setf, close,
  move,
  leftSave, rightSave, upSave, closeSave,
  depth, size
  ) where

import Control.Monad
import Data.Maybe

data CartesianTree a = Node a (CartesianTree a) (CartesianTree a) | Leaf deriving (Show)
data Crumb a = L a (CartesianTree a)
             | R a (CartesianTree a)
             deriving (Show)
type Zipper a = (CartesianTree a, [Crumb a])

left  (Node v l r, cs) = Just (l, L v r:cs)
left  (Leaf, cs)       = Nothing

leftJust = fromJust . left

right (Node v l r, cs) = Just (r, R v l:cs)
right (Leaf, cs)       = Nothing

rightJust = fromJust . right

up    (l, L v r:cs) = Just (Node v l r, cs)
up    (r, R v l:cs) = Just (Node v l r, cs)
up    (r, [])       = Nothing

upJust = fromJust . up

isRoot (_, []) = True
isRoot _       = False

isLeaf (Node _ _ _, _) = False
isLeaf _               = True

root z = case moveUntil isRoot up z of
           Just r -> r

type Motion a = Zipper a -> Maybe (Zipper a)
moveUntil :: (Zipper a -> Bool) -> Motion a -> Motion a
moveUntil pred mot z
    | pred z    = Just z
    | otherwise = mot z >>= moveUntil pred mot

viewf (tr, cs) = tr
close = viewf . root

modf f (tr, cs) = (tr, cs)
setf tr (_, cs) = (tr, cs)

zipper tree = (tree, [])

data Step = SU | SL | SR
move :: [Step] -> Motion  a
move = flip (foldM (flip step))
    where step :: Step -> Motion a
          step SU = up
          step SL = left
          step SR = right

upSave :: Zipper a -> Maybe (Zipper a, Step)
upSave (l, L v r:cs) = Just ((Node v l r, cs), SL)
upSave (r, R v l:cs) = Just ((Node v l r, cs), SR)
upSave (r, [])       = Nothing

leftSave  (Node v l r, cs) = Just ((l, L v r:cs), SU)
leftSave  (Leaf, cs)       = Nothing

rightSave (Node v l r, cs) = Just ((r, R v l:cs), SU)
rightSave (Leaf, cs)       = Nothing

closeSave :: Zipper a -> (CartesianTree a, [Step])
closeSave z = go z []
    where go z path = case upSave z of
                        Nothing      -> (viewf z, path)
                        Just (z', s) -> go z' (s : path)

depth :: CartesianTree a -> Int
depth (Node _ l r) = (depth l `max` depth r) + 1
depth Leaf         = 0

size :: CartesianTree a -> Int
size (Node _ l r)  = size l + size r + 1
size Leaf          = 0

instance Functor CartesianTree where
    fmap f (Node x l r) = Node (f x) (fmap f l) (fmap f r)
    fmap _ Leaf         = Leaf
{--
printTree tree = doprint tree <+> line
    where 
        doprint Leaf = (text "Leaf")
        doprint (Node v Leaf Leaf) = 
           text "Node" <+> text (show v) <+> text ("Leaf Leaf")
        doprint (Node v n1 n2) = 
            text "Node" <+> (align $ (text (show v)) <$> doprint n1 <$> doprint n2)
--}
