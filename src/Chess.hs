module Chess where

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Array
import Data.Char
import Data.List
import Data.Maybe
import FUtil
import qualified Data.Map as M
import qualified Data.PomTree as Pom
import qualified Data.Set as S

data Move = Move {
  fromP :: Maybe Piece,
  fromX :: Maybe Int,
  fromY :: Maybe Int,
  isATake :: Bool,
  toX :: Maybe Int,
  toY :: Maybe Int,
  promote :: Maybe Piece
  } | Castle Piece
  deriving (Show, Ord, Eq)

data Color = CW | CB
  deriving (Eq, Ord)

type Piece = Char

data BdSq = Emp | HasP Color Piece
  deriving (Eq)

type Pt = (Int, Int)

data Board = Board {
  bdGrid :: Array Pt BdSq,
  bdLastPawn2 :: Maybe Pt,
  bdCanCastle :: M.Map Color (S.Set Piece),
  bdTurn :: Color
  }
  deriving (Eq)

type Dir = Int -- 0 is East, 1 is North-East, .., 7

bdInit = Board {
  bdGrid = listArray ((1, 1), (bdW, bdH)) $ b ++ empzone ++ w,
  bdLastPawn2 = Nothing,
  bdCanCastle = M.fromList [(c, S.fromList "qk") | c <- [CW, CB]],
  bdTurn = CW
  }
  where
  backrow = "RNBQKBNR"
  frontrow = replicate bdW 'P'
  b = map (HasP CB) $ backrow ++ frontrow
  empzone = replicate (bdW * (bdH - 4)) Emp
  w = map (HasP CW) $ frontrow ++ backrow

bdW, bdH :: Int
bdW = 8
bdH = 8

modRet :: (MonadState t1 t) => (t1 -> (t2, t1)) -> t t2
modRet f = do
  g <- get
  let (x, g') = f g
  put g'
  return x

parseMv :: String -> Move
parseMv mvStr = case mvStr of
  "O-O" -> Castle 'K'
  "O-O-O" -> Castle 'Q'
  _ -> let
    pChs = "RNBQKP"
    xChs = "abcdefgh"
    yChs = "12345678"
    parseX x = ord x - ord 'a' + 1
    parseY y = bdH - ord y + ord '1'
    tryFrom :: String -> String -> (Maybe Char, String)
    tryFrom chs s = if null s then (Nothing, s) else let s1:sRest = s in
      if s1 `elem` chs then (Just s1, sRest) else (Nothing, s)
    in flip evalState (filter (`elem` pChs ++ xChs ++ yChs ++ "x") mvStr) $ do
      fromP <- modRet (tryFrom pChs)
      x1 <- (parseX <$>) <$> modRet (tryFrom xChs)
      y1 <- (parseY <$>) <$> modRet (tryFrom yChs)
      isATake <- isJust <$> modRet (tryFrom "x")
      -- could be more strict
      modRet (tryFrom "=")
      promote <- modRet (tryFrom pChs)
      g <- get
      if null g && not isATake
        then do
          return $ Move {
            fromP = fromP,
            fromX = Nothing,
            fromY = Nothing,
            isATake = isATake,
            toX = x1,
            toY = y1,
            promote = promote
            }
        else do
          x2 <- (parseX <$>) <$> modRet (tryFrom xChs)
          y2 <- (parseY <$>) <$> modRet (tryFrom yChs)
          modRet (tryFrom "=")
          promote <- modRet (tryFrom pChs)
          return $ Move {
            fromP = fromP,
            fromX = x1,
            fromY = y1,
            isATake = isATake,
            toX = x2,
            toY = y2,
            promote = promote
            }

onBoard :: (Int, Int) -> Bool
onBoard (y, x) = y >= 1 && y <= bdH && x >= 1 && x <= bdW

-- We cheat and return more squares than may actually be legal.
-- The engine does validation; we just need enough to do move disambiguation.
-- todo: We _do_ have to worry about exposed check for disambig unfortunately.
--       (but extremely rarely; I think crafty/xboard fuck this up actually!)
sqCanGetTo :: (Int, Int) -> Board -> Bool -> [(Int, Int)]
sqCanGetTo (y, x) bd isATake = let
  HasP turn p = bdGrid bd ! (y, x)
  tryDir = tryDirPos (y, x)
  tryDirPos _ _ 0 dir = []
  tryDirPos (yPos, xPos) takeAll dist dir = let
    pos' = case dir of
      0 -> (yPos, xPos + 1)
      1 -> (yPos + 1, xPos + 1)
      2 -> (yPos + 1, xPos)
      3 -> (yPos + 1, xPos - 1)
      4 -> (yPos, xPos - 1)
      5 -> (yPos - 1, xPos - 1)
      6 -> (yPos - 1, xPos)
      7 -> (yPos - 1, xPos + 1)
    in if onBoard pos'
      then case bdGrid bd ! pos' of
        Emp -> (if isATake && not takeAll then id else (pos':)) $
          tryDirPos pos' takeAll (dist - 1) dir
        _ -> if isATake then [pos'] else []
      else []
  in case p of
    'K' -> concatMap (tryDir False 1) [0..7]
    'Q' -> concatMap (tryDir False 8) [0..7]
    'R' -> concatMap (tryDir False 8) [0, 2, 4, 6]
    'B' -> concatMap (tryDir False 8) [1, 3, 5, 7]
    'N' -> filter onBoard $
      [(y + oy, x + ox) | oy <- [-2, 2], ox <- [-1, 1]] ++
      [(y + oy, x + ox) | oy <- [-1, 1], ox <- [-2, 2]]
    'P' -> if isATake
      then concatMap (tryDir True 1) (if turn == CW then [5, 7] else [1, 3])
      else tryDir False 2 (if turn == CW then 6 else 2)

-- one or more of x1, y1 could be missing
-- todo: when ambiguous, we should error instead of picking one?
-- -- engine gets that for us
resolveMv :: Board -> Move -> Either String Move
resolveMv bd mv0 = let
  -- when start spot is omitted, we will know the piece
  fillP mv = case fromP mv of
    Just _ -> mv
    Nothing -> mv {fromP = Just 'P'}

  tryXY :: ((Int, Int), BdSq) -> Move -> Move
  tryXY ((y, x), HasP turn p) mv = let
    eqOrN x yMbF = case yMbF mv of
      Just y -> x == y
      Nothing -> True
    in if turn == bdTurn bd &&
      eqOrN x fromX && eqOrN y fromY && p == fromJust (fromP mv) &&
      (fromJust $ toY mv, fromJust $ toX mv) `elem`
      sqCanGetTo (y, x) bd (isATake mv)
      then mv {fromX = Just x, fromY = Just y}
      else mv
  tryXY _ mv = mv
  in case mv0 of
    Move {toX = Just _, toY = Just _} -> Right $
      if isJust (fromX mv0) && isJust (fromY mv0)
        then mv0
        else foldr tryXY (fillP mv0) . assocs $ bdGrid bd
    Castle _ -> Right mv0
    _ -> Left "Could not resolve move"

isPawn :: BdSq -> Bool
isPawn (HasP _ 'P') = True
isPawn _ = False

bdDoMv :: Move -> Board -> Board
bdDoMv mv bd = case mv of
  Move {fromX = Just x1, fromY = Just y1, toX = Just x2, toY = Just y2} ->
    doChanges . considerEnPassant $ considerPromotion changes where
      changes = [
        ((y2, x2), grid ! (y1, x1)),
        ((y1, x1), Emp)
        ]
      -- todo: doesn't check lastPawn2..
      considerEnPassant changes = if
        isPawn (grid ! (y1, x1)) && grid ! (y2, x2) == Emp && x1 /= x2
        then ((y1, x2), Emp):changes else changes
      considerPromotion changes = case promote mv of
        Nothing -> changes
        Just p -> onHead (second . const $ HasP turn p) changes
  Castle p -> let
    -- todo: doesn't check can-castle
    y = if turn == CW then 8 else 1
    xKf = 5
    (xKt, xRf, xRt) = if p == 'K' then (7, 8, 6) else (3, 1, 4)
    in doChanges [
      ((y, xKf), Emp), ((y, xKt), HasP turn 'K'),
      ((y, xRf), Emp), ((y, xRt), HasP turn 'R')
      ]
  where
  grid = bdGrid bd
  turn = bdTurn bd
  doChanges changes = bd {
    bdGrid = grid // changes,
    bdTurn = if bdTurn bd == CW then CB else CW
    }
