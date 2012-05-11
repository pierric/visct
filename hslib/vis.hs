module Vis where

import Trans
import Reader
import Writer
import State
import CartesionTree
import Data.List(intersperse)

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

newtype Color = Color PackedString
data VConfig = C {
  _root_x,  _root_y  :: Int,
  _hookl_x, _hookl_y :: Int,
  _hookr_x, _hookr_y :: Int,
  _width_delta, _height_delta :: Int,
  _foreground_color, _background_color :: PackedString,
  _link_color, _highlight_color_0, _highlight_color_1, _highlight_color_2 :: PackedString
}

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
                                   vsStep
                                   ret <- action
                                   vsStep
                                   command $ SetHighlight id 0
                                   return ret

vsWithHighlightCircle :: (Int, Int) -> (Int -> Vis a) -> Vis a
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
