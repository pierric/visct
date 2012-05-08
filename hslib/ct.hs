import Data.List(intersperse)
import Data.Maybe(fromJust)
import Trans
import Reader
import Writer
import State
import CartesionTree

type Addr   = Int
type Length = Int
data Value = V {
    _leftWidth, _rightWidth :: Int,
    _x, _y :: Int,
    _id :: Int,
    _addr :: Addr,
    _len  :: Length
} deriving Show
type Heap = CartesionTree Value
type HeapZipper = Zipper  Value

getAddr n = case viewf n of 
              Leaf -> fail "address of leaf"
              Node v _ _ -> return $ _addr v
getLen  n = case viewf n of
              Leaf -> fail "length of leaf"
              Node v _ _ -> return $ _len v


newtype Color = Color PackedString
data VConfig = C {
  _root_x,  _root_y  :: Int,
  _hookl_x, _hookl_y :: Int,
  _hookr_x, _hookr_y :: Int,
  _width_delta, _height_delta :: Int,
  _foreground_color, _background_color :: PackedString,
  _link_color, _highlight_color_0, _highlight_color_1, _highlight_color_2 :: PackedString
}
type VState = Int

data Command = CreateCircle Int Addr Length Int Int     -- graphicId value xpos ypos
             | SetForegroundColor Int Color             -- graphicId color
             | SetBackgroundColor Int Color             -- graphicId color
             | SetHighlight Int Int                     -- graphicId enabled
             | SetText Int String                       -- index string
             | Connect Int Int Color                    -- fromGraphicId toGraphicId color
             | Disconnect Int Int                       -- fromGraphicId toGraphicId
             | CreateHighlightCircle Int Color Int Int  -- graphicId color xpos ypos
             | Move Int Int Int                         -- graphicId xpos ypos
             | Delete Int                               -- graphicId
             | CreateLabel Int String Int Int           -- graphicId text xpos ypos
             | Step

type Vis = WriterT [Command] (StateT VState (Reader VConfig))
runVis :: (VState, VConfig) -> Vis a -> (a, VState, [Command])
runVis (is, ic) act = let ((a,w),s) = runReader (runStateT (runWriterT act) is) ic
                      in (a,s,w)

root_x, root_y, hookl_x, hookl_y, hookr_x, hookr_y, width_delta, height_delta :: Vis Int
root_x            = (lift . lift) (asks _root_x)
root_y            = (lift . lift) (asks _root_y)
hookl_x           = (lift . lift) (asks _hookl_x)
hookl_y           = (lift . lift) (asks _hookl_y)
hookr_x           = (lift . lift) (asks _hookr_x)
hookr_y           = (lift . lift) (asks _hookr_y)
width_delta       = (lift . lift) (asks _width_delta)
height_delta      = (lift . lift) (asks _height_delta)

foreground_color, background_color, link_color, highlight_color_0, highlight_color_1, highlight_color_2 :: Vis Color
foreground_color  = (lift . lift) (asks (Color . _foreground_color))
background_color  = (lift . lift) (asks (Color . _background_color))
link_color        = (lift . lift) (asks (Color . _link_color))
highlight_color_0 = (lift . lift) (asks (Color . _highlight_color_0))
highlight_color_1 = (lift . lift) (asks (Color . _highlight_color_1))
highlight_color_2 = (lift . lift) (asks (Color . _highlight_color_2))

hsFree piece tree is ic = runVis (is, ic) (do cid   <- vsCreateCircle piece 100 100
                                              tree' <- fmap close $ attach cid piece (zipper tree)
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
            | naddr <= _addr value && naddr + nlen > _addr value       -> do vsWithHighlightElem (_id value) (vsPutText "Overlapped." >> vsStep)
                                                                             vsDelete cid
                                                                             return heap
            | _addr value <= naddr && _addr value + _len value > naddr -> do vsWithHighlightElem (_id value) (vsPutText "Overlapped." >> vsStep)
                                                                             vsDelete cid
                                                                             return heap
            -- check neighbourhood
            | naddr + nlen == _addr value       -> do vsWithHighlightElem (_id value) (vsPutText "Neighbour found." >> vsStep)
                                                      vsDelete cid
                                                      let lribs = decomposeL t1
                                                      let node  = Node (value{_addr = naddr, _len = nlen+_len value}) Leaf t2
                                                      vsSetText (_id value) (show (naddr, nlen + _len value))
                                                      whenNode t1 (\v -> vsDisconnect (_id value) (_id v))
                                                      vsCombineLeft node lribs
                                                      case combineLeft lribs node of
                                                        Nothing  -> return heap
                                                        Just new -> return $ setf new heap
            | _addr value + _len value == naddr -> do vsWithHighlightElem (_id value) (vsPutText "Neighbour found." >> vsStep)
                                                      vsDelete cid
                                                      let rribs = decomposeR t2
                                                      let node  = Node (value{_addr = _addr value, _len = _len value+nlen}) t1 Leaf
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
                                      if naddr < _addr value then
                                          attach cid piece (fromJust (left  heap))
                                      else
                                          attach cid piece (fromJust (right heap))
            -- found an attach point
            | otherwise -> do let pid  = fmap (\ (Node v _ _) -> _id v) (up heap >>= (return . viewf))
                              whenJust pid (\ rpid -> vsDisconnect rpid (_id value) >> vsConnect rpid cid >> vsConnect cid (_id value) >> vsStep)
                              lpos     <- liftM2 (,) hookl_x hookl_y
                              rpos     <- liftM2 (,) hookr_x hookr_y
                              (lt, rt) <- split node [] [] (Nothing, lpos, rpos)
                              let root = Node (V undefined undefined (_x value) (_y value) cid naddr nlen) Leaf Leaf
                              vsMove cid (_x value, _y value)
                              vsStep
                              vsPutText "Combine Left"
                              vsCombineLeft  root lt
                              case combineLeft lt root of
                                Nothing    -> return heap
                                Just c1 -> do updated <- updateWidth c1 >>= (updatePosition' . fst)
                                              animateNewPosition updated
                                              vsStep
                                              vsPutText "Combine Right"
                                              vsCombineRight updated rt
                                              case combineRight rt updated of
                                                Nothing    -> return heap
                                                Just root' -> return $ setf root' heap
    where 
        split Leaf hookl hookr _  = return (hookl, hookr)
        split (Node v l r) hookl hookr (pid, lpos, rpos)
            = do wd  <- fmap (`div` 2) width_delta
                 hd  <- height_delta
                 rib <- vsWithHighlightElem (_id v) (do
                          whenJust pid (\ rpid -> vsDisconnect rpid (_id v))
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
                     split r (rib:hookl) hookr (Just (_id v), lpos <+> (wd, hd), rpos)
                   else
                     split l hookl (rib:hookr) (Just (_id v), lpos, rpos <+> (-wd, hd))
              where 
              (x0,y0) <+> (x1,y1) = (x0+x1,y0+y1)
        
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
    command Step
    return n'

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


vsMoveTree Leaf _ = return ()
vsMoveTree n@(Node v l r) (px, py) = let dp = (px - _x v, py - _y v) in go n dp >> vsStep
    where go Leaf _ = return ()
          go (Node v l r) (dx,dy) = do vsMove (_id v) (_x v + dx, _y v + dy)
                                       go l (dx, dy)
                                       go r (dx, dy)

vsGetGrId :: Vis Int
vsGetGrId = lift (do i <- get
                     put (i+1)
                     return i)

vsCreateCircle :: (Addr, Length) -> Int -> Int -> Vis Int
vsCreateCircle (a,l) x y = do n <- vsGetGrId
                              command (CreateCircle n a l x y)
                              return n

vsDelete :: Int -> Vis ()
vsDelete id = command $ Delete id

vsPutText :: String -> Vis ()
vsPutText s = command $ SetText 0 s

vsSetText :: Int -> String -> Vis ()
vsSetText id s = command $ SetText id s

vsConnect :: Int -> Int -> Vis ()
vsConnect id1 id2 = do clink <- link_color
                       command $ Connect id1 id2 clink

vsDisconnect :: Int -> Int -> Vis ()
vsDisconnect id1 id2 = command $ Disconnect id1 id2

vsMove :: Int -> (Int, Int) -> Vis ()
vsMove id (x,y)   = command $ Move id x y 

vsWithHighlightElem :: Int -> Vis a -> Vis a
vsWithHighlightElem id action = do command $ SetHighlight id 1
                                   ret <- action
                                   command $ SetHighlight id 0
                                   return ret

vsWithHighlightCircle :: (Addr,Length) -> (Int -> Vis a) -> Vis a
vsWithHighlightCircle (x,y) action = do n     <- vsGetGrId
                                        chigh <- highlight_color_0
                                        command (CreateHighlightCircle n chigh x y)
                                        ret   <- action n
                                        vsDelete n
                                        return ret

vsWithLabel :: String ->  (Int, Int) -> (Int -> Vis ()) -> Vis ()
vsWithLabel s (x,y) action = do n <- vsGetGrId
                                command (CreateLabel n s x y)
                                action n    
                                vsDelete n

vsStep = command Step

command :: Command -> Vis () 
command x = tell [x]

instance Show Color where
    show (Color col) = packedStringToString col
    
toCommand = concat . intersperse "<;>"
instance Show Command where
    show (CreateCircle x a l z w) = toCommand ["CreateCircle", show x, show (a,l), show z, show w]
    show (SetForegroundColor x y) = toCommand ["SetForegroundColor", show x, show y]
    show (SetBackgroundColor x y) = toCommand ["SetBackgroundColor", show x, show y]
    show Step                     = toCommand ["Step"]
    show (SetHighlight x y)       = toCommand ["SetHighlight", show x, show y]
    show (SetText x y)            = toCommand ["SetText", show x, y]
    show (Connect x y z)          = toCommand ["Connect", show x, show y, show z]
    show (CreateHighlightCircle x y z w) = toCommand ["CreateHighlightCircle", show x, show y, show z, show w]
    show (Move x y z)             = toCommand ["Move", show x, show y, show z]
    show (Delete x)               = toCommand ["Delete", show x]
    show (CreateLabel x y z w)    = toCommand ["CreateLabel", show x, y, show z, show w]
    show (Disconnect x y)         = toCommand ["Disconnect", show x, show y]

#ifdef __GLASGOW_HASKELL__
type PackedString = String
packedStringToString = id

istate = 1 :: Int
iconfig= C{
  _root_x = 400,  _root_y =120,
  _hookl_x = 550, _hookl_y = 120,
  _hookr_x = 650, _hookr_y = 120,
  _width_delta = 50, _height_delta = 50,
  _foreground_color = "#77", _background_color = "#77",
  _link_color = "#ee",
  _highlight_color_0 = "#ee", _highlight_color_1 = "#ee", _highlight_color_2 = "#ee"
}

#endif

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
foreign export js "hsFree"   hsFree   :: (Addr, Length) -> Heap -> VState -> VConfig -> (Heap, VState, [Command])
foreign export js "hsPiece"  hsPiece  :: PackedString -> (Addr, Length)

hsConfig = C
hsCmds obj cmds = mapM_ (\c -> jsPush obj (stringToJSString (show c))) cmds
hsLeaf = Leaf
hsPiece str = read (packedStringToString str) :: (Addr, Length)
#endif

main = return ()
