module CartesionTree where

data CartesionTree a = Node a (CartesionTree a) (CartesionTree a) | Leaf deriving (Show)
data Crumb a = L a (CartesionTree a)
             | R a (CartesionTree a)
             deriving (Show)
type Zipper a = (CartesionTree a, [Crumb a])

left  (Node v l r, cs) = Just (l, L v r:cs)
left  (Leaf, cs)       = Nothing

right (Node v l r, cs) = Just (r, R v l:cs)
right (Leaf, cs)       = Nothing

up    (l, L v r:cs) = Just (Node v l r, cs)
up    (r, R v l:cs) = Just (Node v l r, cs)
up    (r, [])       = Nothing

isRoot (_, []) = True
isRoot _       = False

hasLeft (Node _ _ _, _) = True
hasLeft _               = False

hasRight (Node _ _ _, _) = True
hasRight _               = False

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
{--
printTree tree = doprint tree <+> line
    where 
        doprint Leaf = (text "Leaf")
        doprint (Node v Leaf Leaf) = 
           text "Node" <+> text (show v) <+> text ("Leaf Leaf")
        doprint (Node v n1 n2) = 
            text "Node" <+> (align $ (text (show v)) <$> doprint n1 <$> doprint n2)
--}
