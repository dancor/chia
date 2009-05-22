module Chess where

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Array
import Data.Char
import Data.List
import Data.Maybe
import Data.SAN
import FUtil
import Text.Parsec
import qualified Data.Map as M
import qualified Data.PomTree as Pom
import qualified Data.Set as S

data Color = CW | CB
  deriving (Eq, Ord)

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
  bdGrid = listArray ((1, 1), (bdW, bdH)) $ w ++ empzone ++ b,
  bdLastPawn2 = Nothing,
  bdCanCastle = M.fromList [(c, S.fromList "qk") | c <- [CW, CB]],
  bdTurn = CW
  }
  where
  backrow = "RNBQKBNR"
  frontrow = replicate bdW 'P'
  b = map (HasP CB) $ frontrow ++ backrow
  empzone = replicate (bdW * (bdH - 4)) Emp
  w = map (HasP CW) $ backrow ++ frontrow

bdW, bdH :: Int
bdW = 8
bdH = 8

modRet :: (MonadState t1 t) => (t1 -> (t2, t1)) -> t t2
modRet f = do
  g <- get
  let (x, g') = f g
  put g'
  return x

parseMv :: String -> Either String Move
parseMv mvStr = case runParser moveAnnParser () "" mvStr of
  Left err -> Left $ "could not parse move " ++ show mvStr ++ ": " ++ show err
  Right (mv, _) -> Right mv

onBoard :: (Int, Int) -> Bool
onBoard (y, x) = y >= 1 && y <= bdH && x >= 1 && x <= bdW

-- We cheat and return more squares than may actually be legal.
-- The engine does validation; we just need enough to do move disambiguation.
-- todo: We _do_ have to worry about exposed check for disambig unfortunately.
--       (but extremely rarely; I think crafty/xboard fuck this up actually!)
sqCanGetTo :: (Int, Int) -> Board -> Bool -> [(Int, Int)]
sqCanGetTo (y, x) bd isCap = let
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
        Emp -> (if isCap && not takeAll then id else (pos':)) $
          tryDirPos pos' takeAll (dist - 1) dir
        _ -> if isCap then [pos'] else []
      else []
  in case p of
    'K' -> concatMap (tryDir False 1) [0..7]
    'Q' -> concatMap (tryDir False 8) [0..7]
    'R' -> concatMap (tryDir False 8) [0, 2, 4, 6]
    'B' -> concatMap (tryDir False 8) [1, 3, 5, 7]
    'N' -> filter onBoard $
      [(y + oy, x + ox) | oy <- [-2, 2], ox <- [-1, 1]] ++
      [(y + oy, x + ox) | oy <- [-1, 1], ox <- [-2, 2]]
    'P' -> if isCap
      then concatMap (tryDir True 1) (if turn == CW then [1, 3] else [5, 7])
      else tryDir False 2 (if turn == CW then 2 else 6)

-- one or more of x1, y1 could be missing
-- todo: when ambiguous, we should error instead of picking one?
-- -- engine gets that for us
resolveMv :: Board -> Move -> Either String Move
resolveMv bd mv0 = let
  -- when start spot is omitted, we will know the piece
  fillP mv = case mvPiece mv of
    Just _ -> mv
    Nothing -> mv {mvPiece = Just 'P'}

  tryXY :: ((Int, Int), BdSq) -> Move -> Move
  tryXY ((y, x), HasP turn p) mv = let
    eqOrN x yMbF = case yMbF mv of
      Just y -> x == y
      Nothing -> True
    in if turn == bdTurn bd &&
          eqOrN x mvFromX && eqOrN y mvFromY && p == fromJust (mvPiece mv) &&
          (mvToY mv, mvToX mv) `elem` sqCanGetTo (y, x) bd (mvIsACapture mv)
      then mv {mvFromX = Just x, mvFromY = Just y}
      else mv
  tryXY _ mv = mv
  in case mv0 of
    Castle _ -> Right mv0
    _ -> if isJust (mvFromX mv0) && isJust (mvFromY mv0)
      then Right mv0
      else case foldr tryXY (fillP mv0) . assocs $ bdGrid bd of
        mv@(Move {mvFromX = Just _, mvFromY = Just _}) -> Right mv
        _ -> Left "Could not resolve move."

isPawn :: BdSq -> Bool
isPawn (HasP _ 'P') = True
isPawn _ = False

bdDoMv :: Move -> Board -> Board
bdDoMv mv bd = case mv of
  Move {mvFromX = Just x1, mvFromY = Just y1, mvToX = x2, mvToY = y2} ->
    doChanges . considerEnPassant $ considerPromotion changes where
      changes = [
        ((y2, x2), grid ! (y1, x1)),
        ((y1, x1), Emp)
        ]
      -- todo: doesn't check lastPawn2..
      considerEnPassant changes = if
        isPawn (grid ! (y1, x1)) && grid ! (y2, x2) == Emp && x1 /= x2
        then ((y1, x2), Emp):changes else changes
      considerPromotion changes = case mvPromote mv of
        Nothing -> changes
        Just p -> onHead (second . const $ HasP turn p) changes
  Castle p -> let
    -- todo: doesn't check can-castle
    y = if turn == CW then 1 else 8
    xKf = 5
    (xKt, xRf, xRt) = if p == 'K' then (7, 8, 6) else (3, 1, 4)
    in doChanges [
      ((y, xKf), Emp), ((y, xKt), HasP turn 'K'),
      ((y, xRf), Emp), ((y, xRt), HasP turn 'R')
      ]
  _ -> error $ "incomplete move to bdDoMove: " ++ show mv
  where
  grid = bdGrid bd
  turn = bdTurn bd
  doChanges changes = bd {
    bdGrid = grid // changes,
    bdTurn = if bdTurn bd == CW then CB else CW
    }
