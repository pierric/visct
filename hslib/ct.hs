import Vis
import CartesionTree

hsFree spiece tree is ic = runVis (is, ic) (do let piece = read (packedStringToString spiece) :: (Addr, Length)
                                               cid   <- vsCreateCircle piece 100 100
                                               tree' <- fmap close $ attach cid piece (zipper tree) >>= promote
                                               updateTree tree')

attach cid piece@(naddr, nlen) heap
    | nlen <= 0 = do vsPutText ("Invalid segment: " ++ show piece)
                     vsDelete cid
                     vsStep
                     return heap
    | otherwise   =
        case viewf heap of 
          -- attach the piece as the leaf of the tree
          Leaf -> do whenJust (up heap >>= (return . viewf)) (\ (Node v _ _) -> do
                       vsConnect (_id v) cid)
                     vsStep
                     let value = V undefined undefined 100 100 cid naddr nlen
                     return $ setf (Node value Leaf Leaf) heap
          -- otherwise
          node@(Node value t1 t2)
            -- check overlap
            | naddr <= _addr value && naddr + nlen > _addr value       -> overlapped (_id value) cid
            | _addr value <= naddr && _addr value + _len value > naddr -> overlapped (_id value) cid
            -- check neighbourhood
            | naddr + nlen == _addr value       -> do let node  = Node (value{_addr = naddr, _len = nlen+_len value}) Leaf t2
                                                          lribs = decomposeL t1

                                                      vsWithHighlightElem (_id value) (vsPutText "Neighbour found." >> vsStep)
                                                      vsDelete cid
                                                      vsSetText (_id value) (show (naddr, nlen + _len value))
                                                      whenNode t1 (\v -> vsDisconnect (_id value) (_id v))
                                                      vsCombineLeft node lribs

                                                      case combineLeft lribs node of
                                                        Nothing  -> return heap
                                                        Just new -> return $ setf new heap
            | _addr value + _len value == naddr -> do let node  = Node (value{_addr = _addr value, _len = _len value+nlen}) t1 Leaf
                                                          rribs = decomposeR t2

                                                      vsWithHighlightElem (_id value) (vsPutText "Neighbour found." >> vsStep)
                                                      vsDelete cid
                                                      vsSetText (_id value) (show (_addr value, _len value + nlen))
                                                      whenNode t2 (\v -> vsDisconnect (_id value) (_id v))
                                                      vsCombineRight node rribs

                                                      case combineRight rribs node of
                                                        Nothing  -> return heap
                                                        Just new -> return $ setf new heap

            -- to find attach point
            | nlen < _len value -> do vsWithHighlightCircle (_x value, _y value) (\hid -> do
                                          if naddr < _addr value
                                            then
                                              case t1 of
                                                Leaf        -> vsPutText "Reaching a leaf."
                                                Node tv _ _ -> vsMove hid (_x tv, _y tv)
                                            else
                                              case t2 of
                                                Leaf        -> vsPutText "Reaching a leaf."
                                                Node tv _ _ -> vsMove hid (_x tv, _y tv)
                                          vsStep)
                                      if naddr < _addr value 
                                        then
                                          attach cid piece (leftJust  heap)
                                        else
                                          attach cid piece (rightJust heap)
            -- found an attach point
            | otherwise -> do whenJust (up heap >>= (return . viewf)) (\ (Node pv _ _) ->
                                vsDisconnect (_id pv) (_id value) >> vsConnect (_id pv) cid >> vsConnect cid (_id value) >> vsStep)
                              lpos     <- liftM2 (,) hookl_x hookl_y
                              rpos     <- liftM2 (,) hookr_x hookr_y

                              (lt, rt) <- split node [] [] (cid, lpos, rpos)
                              let root = Node (V undefined undefined (_x value) (_y value) cid naddr nlen) Leaf Leaf

                              vsMove cid (_x value, _y value)
                              vsStep
                              vsPutText "Combine Left"
                              vsCombineLeft  root lt

                              case combineLeft lt root of
                                Nothing -> return heap
                                Just c1 -> do c1 <- updateTree' c1
                                              vsPutText "Combine Right"
                                              vsCombineRight c1 rt
                                              case combineRight rt c1 of
                                                Nothing -> return heap
                                                Just c2 -> return $ setf c2 heap
    where 
        split Leaf hookl hookr _  = return (hookl, hookr)
        split (Node v l r) hookl hookr (pid, lpos, rpos)
            = do wd  <- fmap (`div` 2) width_delta
                 hd  <- height_delta
                 rib <- vsWithHighlightElem (_id v) (do
                          vsDisconnect pid (_id v)
                          if _addr v < naddr 
                            then do
                              vsPutText (show (_addr v) ++ " < " ++ show naddr ++ ". Going to the right child.")
                              whenNode r (\ ch -> vsDisconnect (_id v) (_id ch))
                              vsStep
                              vsPutText ("Link it to the left hook.")
                              when (not (null hookl)) (whenNode (head hookl) (\ pr -> vsConnect (_id pr) (_id v) >> vsStep))
                              updatePosition (Node v l Leaf) lpos 0
                            else do
                              vsPutText (show (_addr v) ++ " >= " ++ show naddr ++ ". Going to the left child.")
                              whenNode l (\ ch -> vsDisconnect (_id v) (_id ch))
                              vsStep
                              vsPutText ("Link it to the right hook.")
                              when (not (null hookr)) (whenNode (head hookr) (\ pr -> vsConnect (_id pr) (_id v) >> vsStep))
                              updatePosition (Node v Leaf r) rpos 0)
                 animateNewPosition rib
                 vsStep

                 if _addr v < naddr 
                   then
                     split r (rib:hookl) hookr (_id v, lpos <+> (wd, hd), rpos)
                   else
                     split l hookl (rib:hookr) (_id v, lpos, rpos <+> (-wd, hd))
        
        decomposeL tree = go tree []
            where 
              go Leaf list = list
              go (Node v t1 t2) list = go t2 (Node v t1 Leaf:list)
        decomposeR tree = go tree []
            where
              go Leaf list = list
              go (Node v t1 t2) list = go t1 (Node v Leaf t2:list)

        combineLeft [] n = Just n
        combineLeft list@(Node lv t _:ls) (Node nv _ t2)
            | _addr lv + _len lv >  _addr nv = Nothing 
            -- the rightmost tip of left child could be a left neighbour
            -- yes, remove the tip (replaced by its left child)
            | _addr lv + _len lv == _addr nv = Just $ Node (nv{_addr = _addr lv, _len = _len lv + _len nv}) (composeL (t:ls)) t2
            -- no
            | otherwise     = Just $ Node nv (composeL list) t2
            where composeL (l:ls) = let go [] n     = n
                                        go (Node v l Leaf:ns) n = go ns (Node v l n)
                                    in go ls l
        combineRight [] n = Just n
        combineRight list@(Node lv _ t:ls) (Node nv t1 _)
            | _addr nv + _len nv >  _addr lv = Nothing
            -- the leftmost tip of right child could be a right neighbour
            -- yes, remove the tip (replaced by its right child)
            | _addr nv + _len nv == _addr lv = Just $ Node (nv{_len = _len nv + _len lv}) t1 (composeR (t:ls))
            -- no
            | otherwise     = Just $ Node nv t1 (composeR list)
            where composeR (l:ls) = let go [] n     = n
                                        go (Node v Leaf r:ns) n = go ns (Node v n r)
                                    in go ls l
   
        vsCombineLeft (Node root _ _) lribs = go (reverse lribs) (_id root)
            where go (Node v1 _ _:rs@(Node v2 _ _:_)) pid = do vsWithHighlightCircle (_x v1, _y v1) (\hid -> vsMove hid (_x v2, _y v2) >> vsStep)
                                                               vsConnect pid (_id v1)
                                                               vsStep
                                                               go rs (_id v1)
                  go (Node v  l _:[]) pid                 = vsWithHighlightElem (_id v) $
                                                                case compare (_addr v + _len v) (_addr root) of
                                                                    LT -> vsPutText "Not a neighbour." >> vsConnect pid (_id v) >> vsStep
                                                                    EQ -> do vsPutText "Neighbour found."
                                                                             vsStep
                                                                             vsDisconnect pid (_id v)
                                                                             whenNode l (\v -> vsConnect pid (_id v))
                                                                             vsSetText (_id root) (show (_addr v, _len v + _len root))
                                                                             vsDelete (_id v)
                                                                             vsStep
                                                                    GT -> vsPutText "Overlapped." >> vsStep
                  go [] _ = vsStep
        vsCombineRight (Node root _ _) rribs = go (reverse rribs) (_id root)
            where go (Node v1 _ _:rs@(Node v2 _ _:_)) pid = do vsWithHighlightCircle (_x v1, _y v1) (\hid -> vsMove hid (_x v2, _y v2) >> vsStep)
                                                               vsConnect pid (_id v1)
                                                               vsStep
                                                               go rs (_id v1)
                  go (Node v  _ r:[]) pid                 = vsWithHighlightElem (_id v) $
                                                                case compare (_addr root + _len root) (_addr v) of
                                                                    LT -> vsPutText "Not a neighbour." >> vsConnect pid (_id v) >> vsStep
                                                                    EQ -> do vsPutText "Neighbour found."
                                                                             vsStep
                                                                             vsDisconnect pid (_id v)
                                                                             whenNode r (\v -> vsConnect pid (_id v))
                                                                             vsSetText (_id root) (show (_addr root, _len root + _len v))
                                                                             vsDelete (_id v)
                                                                             vsStep
                                                                    GT -> vsPutText "Overlapped." >> vsStep
                  go [] _ = vsStep

        overlapped v c = do vsWithHighlightElem v (vsPutText "Overlapped." >> vsStep)
                            vsDelete c
                            return heap

promote pos = case viewf pos of
                Leaf -> do vsPutText "Reaching a leaf." 
                           vsStep
                           return pos
                Node pivot _ _ -> vsPutText "" >> go pivot (root pos)
    where
        -- decent from root to pos, and find the first position p where p's length < pos's length
        go pv cursor -- n@(Node cv lt rt)
            = case viewf cursor of
                Leaf -> return cursor
                n@(Node cv lt rt)
                  -- If we reach the pos, which means the node is at a right level
                  | _addr cv == _addr pv && _len cv == _len pv -> do vsPutText "Promotion done."
                                                                     vsStep
                                                                     return pos
                  -- Or the current ancester has a larger or equal length
                  | _len cv >= _len pv -> do vsWithHighlightCircle (_x cv, _y cv) (\hid -> do
                                             if _addr cv > _addr pv
                                               then do 
                                                 let Node lv _ _ = lt
                                                 vsMove hid (_x lv, _y lv)
                                               else do
                                                 let Node rv _ _ = rt
                                                 vsMove hid (_x rv, _y rv))
                                             vsStep
                                             if _addr cv > _addr pv
                                               then go pv (leftJust  cursor)
                                               else go pv (rightJust cursor)
                  -- Or a ancester with smaller length is met
                  | otherwise -> do vsWithHighlightElem (_id cv) (vsPutText "lift up to here")
                                    vsStep
                                    lpos    <- liftM2 (,) hookl_x hookl_y
                                    rpos    <- liftM2 (,) hookr_x hookr_y
                                    (lt,rt) <- split pv n (zipper Leaf) (zipper Leaf) lpos rpos
                                   -- firstly, move the attaching node up to the right position
                                    let (tree, path) = closeSave (setf (Node pv Leaf Leaf) cursor)
                                    -- update and back to the attaching point
                                    Just cursor' <- fmap (move path . zipper) $ updateTree tree
                                    -- finally, attach the left and right children
                                    -- and update their position
                                    let Node pv' _ _ = viewf cursor'
                                    whenNode lt (\ lv -> vsConnect (_id pv') (_id lv))
                                    n@(Node pv' lt Leaf) <- updateTree' (Node pv' lt Leaf)
                                    whenNode rt (\ rv -> vsConnect (_id pv') (_id rv))
                                    n                    <- updateTree' (Node pv' lt rt)
                                    return $ setf n cursor'
 
        split pivot (Node current lt rt) hookl hookr lpos rpos
            | _addr pivot > _addr current
                = do vsPutText $ show (_addr pivot) ++ " > " ++ (show (_addr current)) ++ ". Going to right child."
                     nc <- vsWithHighlightCircle (_x current, _y current) (\hid -> do
                             let Node rv _ _ = rt
                             vsMove hid (_x rv, _y rv)
                             vsStep
                             vsDisconnect (_id current) (_id rv)
                             whenJust (up hookl) (\ p -> whenNode (viewf p) (\ pv -> vsConnect (_id pv) (_id current)))
                             node <- updatePosition (Node current lt Leaf) lpos 0
                             animateNewPosition node
                             return node)
                     vsStep
                     let hookl' = rightJust $ setf nc hookl
                     wd  <- fmap (`div` 2) width_delta
                     hd  <- height_delta
                     split pivot rt hookl' hookr (lpos <+> (wd, hd)) rpos
            | _addr pivot < _addr current
                = do vsPutText $ show (_addr pivot) ++ " < " ++ (show (_addr current)) ++ ". Going to left child."
                     nc <- vsWithHighlightCircle (_x current, _y current) (\hid -> do
                             let Node lv _ _ = lt
                             vsMove hid (_x lv, _y lv)
                             vsStep
                             vsDisconnect (_id current) (_id lv)
                             whenJust (up hookl) (\ p -> whenNode (viewf p) (\ pv -> vsConnect (_id pv) (_id current)))
                             node <- updatePosition (Node current Leaf rt) rpos 0
                             animateNewPosition node
                             return node)
                     vsStep
                     let hookr' = leftJust $ setf nc hookr
                     wd  <- fmap (`div` 2) width_delta
                     hd  <- height_delta
                     split pivot lt hookl hookr' lpos (rpos <+> (-wd,hd))
            | otherwise 
                = do whenNode lt (\lv -> vsDisconnect (_id current) (_id lv))
                     lt' <- updatePosition lt lpos 0
                     animateNewPosition lt'
                     vsStep
                     whenNode rt (\rv -> vsDisconnect (_id current) (_id rv))
                     rt' <- updatePosition rt rpos 0
                     animateNewPosition rt'
                     vsStep
                     return (close (setf lt' hookl), close (setf rt' hookr))

hsAlloc slen tree is ic = runVis (is, ic) (let inorder = toList (zipper tree)
                                           in go inorder)
    where toList pos | isLeaf pos = []
                     | otherwise  = toList (leftJust pos) ++ [pos] ++ toList (rightJust pos)

          len :: Length
          len = read (packedStringToString slen) :: Int

          go []     = do vsPutText $ "Allocation failed (length = " ++ show len ++ ")."
                         vsStep
                         return tree
          go (p:ps) = do let Node pv lt rt = viewf p
                         case compare (_len pv) len of
                           LT -> do when (not $ null ps) (
                                      vsWithHighlightCircle (_x pv, _y pv) (\hid -> 
                                        let Node nv _ _ = viewf (head ps)
                                        in vsMove hid (_x nv, _y nv)))
                                    go ps
                           EQ -> do vsWithHighlightElem (_id pv) (do vsPutText "Matched. Deleting this node."
                                                                     vsDisconnectParent   p
                                                                     vsDisconnectChildren p
                                                                     vsStep)
                                    vsDelete (_id pv)
                                    vsStep
                                    node <- merge (leftJust p) (rightJust p)
                                    updateTree (close $ setf node p)
                           GT -> do let newa = _addr pv + len
                                        newl = _len pv - len
                                    vsWithHighlightElem (_id pv) (do vsPutText ("Matched. Substract " ++ show len ++" from current node")
                                                                     vsSetText (_id pv) (show (newa, newl))
                                                                     vsPutText ("Demote the current node."))
                                    p' <- demote $ setf (Node (pv{_addr = newa, _len = newl}) lt rt) p
                                    updateTree (close p')

merge pos1 pos2 = case (viewf pos1, viewf pos2) of
                    (Leaf, t2)  -> do vsPutText "Reaching a leaf." >> return t2
                    (t1, Leaf)  -> do vsPutText "Reaching a leaf." >> return t1
                    (t1@(Node v1 t11 _), t2@(Node v2 _ t22))
                        | _len v1 >  _len v2 -> do vsWithHighlightElem (_id v1) (
                                                     vsWithHighlightElem (_id v2) (do
                                                       vsPutText ("length of the left > length of the right.")
                                                       vsDisconnectParent (rightJust pos1)
                                                       vsDisconnectParent pos2
                                                       vsStep))
                                                   t12 <- merge (rightJust pos1) pos2
                                                   whenNode t12 (\ v -> vsConnect (_id v1) (_id v))
                                                   return $ Node v1 t11 t12
                        | _len v1 <= _len v2 -> do vsWithHighlightElem (_id v1) (
                                                     vsWithHighlightElem (_id v2) (do
                                                       vsPutText ("length of the left <= length of the right.")
                                                       vsDisconnectParent pos1
                                                       vsDisconnectParent (leftJust pos2)
                                                       vsStep))
                                                   t21 <- merge pos1 (leftJust pos2)
                                                   whenNode t21 (\ v -> vsConnect (_id v2) (_id v))
                                                   return $ Node v2 t21 t22
{-- demote a node
demote v Leaf Leaf = Node v Leaf Leaf
demote v Leaf t2@(Node v2 t21 t22)
    | _len v >  _len v2 = Node v Leaf t2
    | _len v <= _len v2 = Node v2 (demote v Leaf t21) t22
demote v t1@(Node v1 t11 t12) Leaf
    | _len v >  _len v1 = Node v t1 Leaf
    | _len v <= _len v1 = Node v1 t11 (demote v t12 Leaf)
demote v t1@(Node v1 t11 t12) t2@(Node v2 t21 t22)
    | _len v >= _len v1 && _len v  >=  _len v2 = Node v t1 t2
    | _len v >= _len v1 && _len v2 > _len v    = Node v2 (Node v t1 t21) t22
    | _len v >= _len v2 && _len v1 > _len v    = Node v1 t11 (Node v t12 t2)
    | _len v1 >  _len v2                       = Node v1 t11 (Node v2 (demote v t12 t21) t22)
    | _len v1 <= _len v2                       = Node v2 (Node v1 t11 (demote v t12 t21)) t22
--}

-- precondition: not (isLeaf cursor)
demote cursor = case viewf cursor of
                  Node v Leaf Leaf -> do vsPutText "Reaching a leaf."
                                         vsStep
                                         return cursor
                  Node v Leaf t2@(Node v2 t21 t22)
                    | _len v >  _len v2 -> do vsWithHighlightElem (_id v) (vsPutText "insert here." >> vsConnect (_id v) (_id v2) >> vsStep)
                                              return cursor
                    | _len v <= _len v2 -> do vsWithHighlightElem (_id v) (
                                                vsWithHighlightElem (_id v2) (
                                                  vsPutText (show (_len v) ++ " <= " ++ (show (_len v2)))))
                                              vsStep
                                              vsDisconnectParent cursor 
                                              vsDisconnectChildren cursor
                                              whenNode t21 (\vc -> vsDisconnect (_id v2) (_id vc))
                                              vsStep
                                              tr <- updateTree' (Node v2 (Node v Leaf t21) t22)
                                              vsConnect (_id v2) (_id v)
                                              whenNode t21 (\vc -> vsConnect (_id v) (_id vc))
                                              vsOpParent cursor (\ pv -> vsConnect (_id pv) (_id v2))
                                              demote $ leftJust $ setf tr cursor
                  Node v t1@(Node v1 t11 t12) Leaf 
                    | _len v >  _len v1 -> do vsWithHighlightElem (_id v) (vsPutText "insert here." >> vsConnect (_id v) (_id v1) >> vsStep)
                                              return cursor
                    | _len v <= _len v1 -> do vsWithHighlightElem (_id v) (
                                                vsWithHighlightElem (_id v1) (
                                                  vsPutText (show (_len v) ++ " <= " ++ (show (_len v1)))))
                                              vsStep
                                              vsDisconnectParent cursor
                                              vsDisconnectChildren cursor
                                              whenNode t12 (\vc -> vsDisconnect (_id v1) (_id vc))
                                              vsStep
                                              tr <- updateTree' (Node v1 t11 (Node v t12 Leaf))
                                              vsConnect (_id v1) (_id v)
                                              whenNode t12 (\vc -> vsConnect (_id v) (_id vc))
                                              vsOpParent cursor (\ pv -> vsConnect (_id pv) (_id v1))
                                              demote $ rightJust $ setf tr cursor
                  Node v t1@(Node v1 t11 t12) t2@(Node v2 t21 t22)
                    | _len v >= _len v1 && _len v  >=  _len v2 -> do vsWithHighlightElem (_id v) (vsPutText "insert here." >> vsConnect (_id v) (_id v2) >> vsStep)
                                                                     return cursor
                    | _len v >= _len v1 && _len v2 > _len v    -> do vsWithHighlightElem (_id v) (
                                                                       vsWithHighlightElem (_id v1) (
                                                                         vsWithHighlightElem (_id v2) (
                                                                           vsPutText (show (_len v) ++ " >= " ++ (show (_len v1)) ++ " && " ++
                                                                                      show (_len v) ++ " <  " ++ (show (_len v2))))))
                                                                     vsStep
                                                                     vsDisconnectParent cursor
                                                                     vsDisconnectChildren cursor
                                                                     whenNode t21 (\ vc -> vsDisconnect (_id v2) (_id vc))
                                                                     vsStep
                                                                     tr <- updateTree' (Node v2 (Node v t1 t21) t22)
                                                                     vsConnect (_id v2) (_id v)
                                                                     vsConnect (_id v)  (_id v1)
                                                                     whenNode t21 (\ vc -> vsConnect (_id v) (_id vc))
                                                                     vsOpParent cursor (\ pv -> vsConnect (_id pv) (_id v2))
                                                                     demote $ leftJust $ setf tr cursor
                    | _len v >= _len v2 && _len v1 > _len v    -> do vsWithHighlightElem (_id v) (
                                                                      vsWithHighlightElem (_id v1) (
                                                                        vsWithHighlightElem (_id v2) (
                                                                          vsPutText (show (_len v) ++ " <  " ++ (show (_len v1)) ++ " && " ++
                                                                                     show (_len v) ++ " >= " ++ (show (_len v2))))))
                                                                     vsStep
                                                                     vsDisconnectParent cursor
                                                                     vsDisconnectChildren cursor
                                                                     whenNode t12 (\vc -> vsDisconnect (_id v1) (_id vc))
                                                                     vsStep
                                                                     tr <- updateTree' (Node v1 t11 (Node v t12 t2))
                                                                     vsConnect (_id v1) (_id v)
                                                                     vsConnect (_id v)  (_id v2)
                                                                     whenNode t12 (\ vc -> vsConnect (_id v) (_id vc))
                                                                     vsOpParent cursor (\ pv -> vsConnect (_id pv) (_id v1))
                                                                     demote $ rightJust $ setf tr cursor
                    | _len v1 >  _len v2                       -> do vsWithHighlightElem (_id v) (
                                                                      vsWithHighlightElem (_id v1) (
                                                                        vsWithHighlightElem (_id v2) (
                                                                         vsPutText (show (_len v) ++ " < min{" ++ show (_len v1) ++ ", " ++ show (_len v2) ++ "} &&" ++
                                                                                    show (_len v1) ++ " > " ++ (show (_len v2))))))
                                                                     vsStep
                                                                     vsDisconnectParent cursor
                                                                     vsDisconnectChildren cursor
                                                                     whenNode t12 (\vc -> vsDisconnect (_id v1) (_id vc))
                                                                     whenNode t21 (\vc -> vsDisconnect (_id v2) (_id vc))
                                                                     vsStep
                                                                     tr <- updateTree' (Node v1 t11 (Node v2 (Node v t12 t21) t22))
                                                                     vsConnect (_id v1) (_id v2)
                                                                     vsConnect (_id v2) (_id v)
                                                                     whenNode t12 (\vc -> vsConnect (_id v) (_id vc))
                                                                     whenNode t21 (\vc -> vsConnect (_id v) (_id vc))
                                                                     vsOpParent cursor (\pv -> vsConnect (_id pv) (_id v1))
                                                                     demote $ leftJust $ rightJust $ setf tr cursor
                    | _len v1 <= _len v2                       -> do vsWithHighlightElem (_id v) (
                                                                      vsWithHighlightElem (_id v1) (
                                                                        vsWithHighlightElem (_id v2) (
                                                                          vsPutText (show (_len v) ++ " < min{" ++ show (_len v1) ++ ", " ++ show (_len v2) ++ "} &&" ++
                                                                                     show (_len v1) ++ " <= " ++ (show (_len v2))))))
                                                                     vsStep
                                                                     vsDisconnectParent cursor
                                                                     vsDisconnectChildren cursor
                                                                     whenNode t12 (\vc -> vsDisconnect (_id v1) (_id vc))
                                                                     whenNode t21 (\vc -> vsDisconnect (_id v2) (_id vc))
                                                                     vsStep
                                                                     tr <- updateTree' (Node v2 (Node v1 t11 (Node v t12 t21)) t22)
                                                                     vsConnect (_id v2) (_id v1)
                                                                     vsConnect (_id v1) (_id v)
                                                                     whenNode t12 (\vc -> vsConnect (_id v) (_id vc))
                                                                     whenNode t21 (\vc -> vsConnect (_id v) (_id vc))
                                                                     vsOpParent cursor (\pv -> vsConnect (_id pv) (_id v2))
                                                                     demote $ rightJust $ leftJust $ setf tr cursor
                                                                      
updateTree Leaf = return Leaf
updateTree n    = do
    xst <- root_x 
    yst <- root_y
    (n'@(Node v _ _), _) <- updateWidth n
    let xst' = if _leftWidth v > xst then
                   _leftWidth v
               else if _rightWidth v > xst then
                   max (_leftWidth v) (2 * xst - _rightWidth v)
               else 
                   xst
    n' <- updatePosition n' (xst', yst) 0
    animateNewPosition n'
    vsStep
    return n'

updateTree' tree =  do (t, _)  <- updateWidth tree
                       t <- updatePosition' t
                       animateNewPosition t
                       vsStep
                       return t

updateWidth Leaf = return (Leaf, 0)
updateWidth (Node v left right) = do
    dwidth  <- width_delta
    (ln,lw) <- updateWidth left
    (rn,rw) <- updateWidth right
    let lw' = max lw (dwidth `div` 2)
    let rw' = max rw (dwidth `div` 2)
    let v' = v { _leftWidth = lw'
               , _rightWidth= rw' }
    return (Node v' ln rn, lw' + rw')

updatePosition Leaf _ _ = return Leaf
updatePosition (Node v left right) (xpos, ypos) side = do
    dheight <- height_delta
    let xpos' = if side == -1 then 
                    xpos - _rightWidth v
                else if side == 1 then
                    xpos + _leftWidth v
                else
                    xpos
    let v'    = v {_x = xpos', _y = ypos}
    left' <- updatePosition left  (xpos', ypos + dheight) (-1)
    right'<- updatePosition right (xpos', ypos + dheight)   1
    return (Node v' left' right')

updatePosition' Leaf = return Leaf
updatePosition' n@(Node v _ _) = updatePosition n (_x v, _y v) 0

animateNewPosition :: Heap -> Vis ()
animateNewPosition Leaf = return ()
animateNewPosition (Node v l r) = do
    command (Move (_id v) (_x v) (_y v))
    animateNewPosition l
    animateNewPosition r

when True  act = act
when False _   = return ()

whenNode Leaf _         = return ()
whenNode (Node v _ _) f = f v

whenJust Nothing _      = return ()
whenJust (Just v) f     = f v

liftM2 f a1 a2 = do
    v1 <- a1
    v2 <- a2
    return (v1,v2)

(x0,y0) <+> (x1,y1) = (x0+x1,y0+y1)

vsOpParent cursor act   = whenJust (up cursor)  (\ pr -> 
                              whenNode (viewf pr) (\ pv -> act pv))

vsOpChildren cursor act = do whenNode (viewf $ leftJust cursor) (\ lv -> 
                               act lv)
                             whenNode (viewf $ rightJust cursor) (\ rv ->
                               act rv)

vsDisconnectParent cursor   = whenNode (viewf cursor) (\ cv -> vsOpParent   cursor (\ pv -> vsDisconnect (_id pv) (_id cv)))
vsDisconnectChildren cursor = whenNode (viewf cursor) (\ cv -> vsOpChildren cursor (\ hv -> vsDisconnect (_id cv) (_id hv)))

#ifdef __UHC__
data JsCollection 
foreign import js "%1.push(%*)" jsPush :: JsCollection -> PackedString -> IO ()
foreign import prim "primStringToPackedString" stringToJSString :: String -> PackedString
foreign export js "hsConfig" hsConfig :: Int -> Int -> Int -> Int ->
                                         Int -> Int -> Int -> Int -> 
                                         PackedString -> PackedString -> PackedString -> 
                                         PackedString -> PackedString -> PackedString -> VConfig
foreign export js "hsCmds"   hsCmds   :: JsCollection -> [Command] -> IO ()
foreign export js "hsLeaf"   hsLeaf   :: Heap
foreign export js "hsFree"   hsFree   :: PackedString -> Heap -> VState -> VConfig -> (Heap, VState, [Command])
foreign export js "hsAlloc"  hsAlloc  :: PackedString -> Heap -> VState -> VConfig -> (Heap, VState, [Command])

hsConfig = C
hsCmds obj cmds = mapM_ (\c -> jsPush obj (stringToJSString (show c))) cmds
hsLeaf = Leaf
hsPiece str = read (packedStringToString str) :: (Addr, Length)
#endif

main = return ()
