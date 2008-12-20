module Main where

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Array
import Data.Char
import Data.List
import Data.Maybe
import FUtil
import System.Directory
import System.Environment
import System.IO
import System.Process
import qualified AnsiColor as AC
import qualified Data.Map as M
import qualified Data.Set as S

chProg :: [Char]
chProg = "crafty"
bdW :: Int
bdW = 8
bdH :: Int
bdH = 8

data Color = CW | CB deriving (Eq, Ord)
type Piece = Char
data BdSq = Emp | HasP Color Piece deriving Eq
type Pt = (Int, Int)
data Bd = Bd (Array Pt BdSq) deriving Eq
data Game = Game {
  gmBd :: Bd,
  gmTurn :: Color,
  gmLastPawn2 :: Maybe Pt,
  gmCanCastle :: M.Map Color (S.Set Piece),
  gmProc :: Proc,
  gmHist :: [String]
  }
data Move = Move {
  fromP :: Maybe Piece,
  fromX :: Maybe Int,
  fromY :: Maybe Int,
  isATake :: Bool,
  toX :: Maybe Int,
  toY :: Maybe Int,
  promote :: Maybe Piece
  } | Castle Piece deriving Show
data Proc = Proc {
  prIn :: Handle,
  prOut :: Handle,
  prErr :: Handle,
  prId :: ProcessHandle
  }

instance Show BdSq where
  show Emp = " "
  -- I didn't like how the bishop and pawns look too similar in tiny font,
  -- so I'm using little triangles for pawns.
  show (HasP CW 'K') = toUtf "♚"
  show (HasP CW 'Q') = toUtf "♛"
  show (HasP CW 'R') = toUtf "♜"
  show (HasP CW 'B') = toUtf "♝"
  show (HasP CW 'N') = toUtf "♞"
  --show (HasP CW 'P') = toUtf "♟"
  show (HasP CW 'P') = toUtf "▴"
  show (HasP CB 'K') = toUtf "♔"
  show (HasP CB 'Q') = toUtf "♕"
  show (HasP CB 'R') = toUtf "♖"
  show (HasP CB 'B') = toUtf "♗"
  show (HasP CB 'N') = toUtf "♘"
  --show (HasP CB 'P') = toUtf "♙"
  show (HasP CB 'P') = toUtf "▵"

instance Show Bd where
  show (Bd bd) = let
    showAlt ((i, j), p) = if (i + j) `mod` 2 == 0
      then AC.whiteBg ++ AC.black ++ case p of
        Emp -> show p
        HasP CW c -> show $ HasP CB c
        HasP CB c -> show $ HasP CW c
      else AC.blackBg ++ AC.white ++ show p
    stopWeirdWhiteLinesInTermSometimes = (++ AC.blackBg)
    in (interlines . map (stopWeirdWhiteLinesInTermSometimes . concat) .
    splitN bdW . map showAlt . assocs) bd ++ AC.normal

initGm :: IO Game
initGm = do
  let
    backrow = "RNBQKBNR"
    frontrow = replicate bdW 'P'
    b = map (HasP CB) $ backrow ++ frontrow
    empzone = replicate (bdW * (bdH - 4)) Emp
    w = map (HasP CW) $ frontrow ++ backrow
  (pIn, pOut, pErr, pId) <- runInteractiveProcess chProg [] Nothing Nothing
  hPutStrLn pIn "xboard"
  hPutStrLn pIn "st 0.1"
  hPutStrLn pIn "skill 50"
  hFlush pIn
  return $ Game {
    gmBd = Bd $ listArray ((1, 1), (bdW, bdH)) $ b ++ empzone ++ w,
    gmTurn = CW,
    gmLastPawn2 = Nothing,
    gmCanCastle = M.fromList [(c, S.fromList "qk") | c <- [CW, CB]],
    gmProc = Proc pIn pOut pErr pId,
    gmHist = []
    }

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

-- todo: castling, enpassant
-- - could be totally in eng..?

type Dir = Int -- 0 is East, 1 is North-East, .., 7

onBd :: (Int, Int) -> Bool
onBd (y, x) = y >= 1 && y <= bdH && x >= 1 && x <= bdW

-- We cheat and return more squares than may actually be legal.
-- The engine does validation; we just need enough to do move disambiguation.
-- todo: We _do_ have to worry about exposed check for disambig unfortunately.
--       (but extremely rarely; I think crafty/xboard fuck this up actually!)
sqCanGetTo :: (Int, Int) -> Game -> Bool -> [(Int, Int)]
sqCanGetTo (y, x) gm isATake = let
  Bd bd = gmBd gm
  HasP turn p = bd ! (y, x)
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
    in if onBd pos'
      then case bd ! pos' of
        Emp -> (if isATake && not takeAll then id else (pos':)) $
          tryDirPos pos' takeAll (dist - 1) dir
        _ -> if isATake then [pos'] else []
      else []
  in case p of
    'K' -> concatMap (tryDir False 1) [0..7]
    'Q' -> concatMap (tryDir False 8) [0..7]
    'R' -> concatMap (tryDir False 8) [0, 2, 4, 6]
    'B' -> concatMap (tryDir False 8) [1, 3, 5, 7]
    'N' -> filter onBd $
      [(y + oy, x + ox) | oy <- [-2, 2], ox <- [-1, 1]] ++
      [(y + oy, x + ox) | oy <- [-1, 1], ox <- [-2, 2]]
    'P' -> if isATake
      then concatMap (tryDir True 1) (if turn == CW then [5, 7] else [1, 3])
      else tryDir False 2 (if turn == CW then 6 else 2)

-- one or more of x1, y1 could be missing
-- todo: when ambiguous, we should error instead of picking one?
-- -- engine gets that for us
resolveMv :: Game -> Move -> Maybe Move
resolveMv gm mv0 = let

  -- when start spot is omitted, we will know the piece
  fillP mv = case fromP mv of
    Just _ -> mv
    Nothing -> mv {fromP = Just 'P'}

  Bd bd = gmBd gm
  tryXY :: ((Int, Int), BdSq) -> Move -> Move
  tryXY ((y, x), HasP turn p) mv = let
    eqOrN x yMbF = case yMbF mv of
      Just y -> x == y
      Nothing -> True
    in if turn == gmTurn gm &&
      eqOrN x fromX && eqOrN y fromY && p == fromJust (fromP mv) &&
      (fromJust $ toY mv, fromJust $ toX mv) `elem`
      sqCanGetTo (y, x) gm (isATake mv)
      then mv {fromX = Just x, fromY = Just y}
      else mv
  tryXY _ mv = mv
  in case mv0 of
    Move {toX = Just _, toY = Just _} ->
      if isJust (fromX mv0) && isJust (fromY mv0)
        then Just mv0
        else Just . foldr tryXY (fillP mv0) $ assocs bd
    Castle _ -> Just mv0
    _ -> Nothing

isEmp :: BdSq -> Bool
isEmp Emp = True
isEmp _ = False

isPawn :: BdSq -> Bool
isPawn (HasP _ 'P') = True
isPawn _ = False

untilM :: (Monad t) => (t1 -> Bool) -> t t1 -> t t1
untilM t f = do
  y <- f
  if t y then return y else untilM t f

debugLog :: [Char] -> IO ()
debugLog s = do
  home <- getEnv "HOME"
  createDirectoryIfMissing False $ home ++ "/.chia"
  appendFile (home ++ "/.chia/englog") $ s ++ "\n"

getMove :: Game -> IO [Char]
getMove gm = do
  let
    Proc pIn pOut pErr pId = gmProc gm
  untilM (\ l -> any (`isPrefixOf` l)
    ["move", "Illegal move", "1/2-1/2", "1-0", "0-1"]) $
    do
      l <- hGetLine pOut
      debugLog l
      return l

doMv :: Bool -> String -> Move -> Game -> IO (Maybe Game)
doMv tellEng mvStr mv gm = do
  let
    Bd bd = gmBd gm
    Proc pIn pOut pErr pId = gmProc gm
    doChanges changes = if tellEng
      then do
        hPutStrLn pIn mvStr
        --hPutStrLn pIn "go"
        hPutStrLn pIn "?"
        hFlush pIn
        compStr <- getMove gm
        debugLog $ "COMPSTR: " ++ compStr
        clrScr
        if "move " `isPrefixOf` compStr
          then do
            let
              'm':'o':'v':'e':' ':compMvStr = compStr
              Just compMv = resolveMv gm' $ parseMv compMvStr
            putStrLn compMvStr
            doMv False compMvStr compMv gm'
          else do
            --putStrLn compStr
            return Nothing
      else return $ Just gm'
      where gm' = gm {
        gmBd = Bd $ bd // changes,
        gmTurn = if gmTurn gm == CW then CB else CW,
        gmHist = gmHist gm ++ [mvStr]
        }
  case mv of
    Move {fromX = Just x1, fromY = Just y1, toX = Just x2, toY = Just y2} ->
      doChanges . considerEnPassant . considerPromotion $ changes where
        changes = [
          ((y2, x2), bd ! (y1, x1)),
          ((y1, x1), Emp)
          ]
        considerEnPassant changes = if
          isPawn (bd ! (y1, x1)) && isEmp (bd ! (y2, x2)) && x1 /= x2
          then ((y1, x2), Emp):changes else changes
        considerPromotion changes = case promote mv of
          Nothing -> changes
          Just p -> onHead (second . const $ HasP (gmTurn gm) p) changes
    Castle p -> let
      c = gmTurn gm
      y = if c == CW then 8 else 1
      xKf = 5
      (xKt, xRf, xRt) = if p == 'K' then (7, 8, 6) else (3, 1, 4)
      in doChanges [
        ((y, xKf), Emp), ((y, xKt), HasP c 'K'),
        ((y, xRf), Emp), ((y, xRt), HasP c 'R')
        ]
    mv -> return Nothing

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = (f x):xs

mvsOn :: [Game] -> IO ()
mvsOn gms = do
  let
    gm = head gms
    wat mvStr = clrScr >> hPutStrLn stderr (show mvStr ++ "?") >> mvsOn gms
    noUndo = hPutStrLn stderr "Nothing to undo." >> mvsOn gms
    Proc pIn _ _ pId = gmProc gm
  print $ gmBd gm
  mvStr <- getLine
  case mvStr of
    "q" -> terminateProcess pId >> return ()
    "r" -> main
    -- todo error checking in undo
    "u" -> case gms of
      [_] -> noUndo
      _ -> do
        clrScr
        putStrLn ""
        --hPutStrLn pIn "force"
        hPutStrLn pIn "undo"
        hPutStrLn pIn "undo"
        hFlush pIn
        mvsOn $ tail gms
    "s" -> do
      writeFile "game.pgn" . interwords .
        zipWith (\ n l -> show n ++ ". " ++ interwords l) [1..] .
        splitN 2 $ gmHist gm
      mvsOn gms
    _ -> case resolveMv gm $ parseMv mvStr of
      Just mv -> do
        gmMb <- doMv True mvStr mv gm
        case gmMb of
          Just gm' -> mvsOn (gm':gms)
          Nothing -> wat mvStr
      Nothing -> wat mvStr

main :: IO ()
main = do
  clrScr
  putStrLn ""
  gm <- initGm
  mvsOn [gm]
