module Main where

import Chess

import Control.Applicative
import Control.Arrow
import Control.Monad.Error
import Control.Monad.State
import Data.Array
import Data.Char
import Data.List
import Data.Maybe
import FUtil
import HSH
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.IO
import System.Process
import qualified AnsiColor as AC
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.PomTree as PMT

{-
data Game = Game {
  gmBd :: Bd,
  gmTurn :: Color,
  gmLastPawn2 :: Maybe Pt,
  gmCanCastle :: M.Map Color (S.Set Piece),
  gmProc :: Proc,
  -- should be Move not String? but i didn't want to write move -> string for
  -- pgn writing eh
  gmHist :: PMT.PomTree String,
  gmHumans :: Int,
  gmRes :: Maybe String,
  gmSkill :: Int
  }

data Proc = Proc {
  prIn :: Handle,
  prOut :: Handle,
  prErr :: Handle,
  prId :: ProcessHandle
  }
-}

data St = St {
  stHumans :: Int
  }

data Options = Options {
  optSkill :: Int
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

chProg :: [Char]
chProg = "crafty"

defOpts :: Options
defOpts = Options {
  optSkill = 100
}

options :: [OptDescr (Options -> Options)]
options = [
  Option "s" ["skill"] (ReqArg (\ a o -> o {optSkill = read a}) "N")
    "1..100"
  ]

initGm :: Options -> IO Game
initGm opts = do
  let
    backrow = "RNBQKBNR"
    frontrow = replicate bdW 'P'
    b = map (HasP CB) $ backrow ++ frontrow
    empzone = replicate (bdW * (bdH - 4)) Emp
    w = map (HasP CW) $ frontrow ++ backrow
  (pIn, pOut, pErr, pId) <- runInteractiveProcess chProg [] Nothing Nothing
  hPutStrLn pIn "xboard"
  hPutStrLn pIn "st 0.1"
  hPutStrLn pIn "easy"
  hPutStrLn pIn $ "skill " ++ show (optSkill opts)
  hFlush pIn
  return $ Game {
    gmBd = Bd $ listArray ((1, 1), (bdW, bdH)) $ b ++ empzone ++ w,
    gmTurn = CW,
    gmLastPawn2 = Nothing,
    gmCanCastle = M.fromList [(c, S.fromList "qk") | c <- [CW, CB]],
    gmProc = Proc pIn pOut pErr pId,
    gmHist = PMT.empty,
    gmHumans = 1,
    gmRes = Nothing,
    gmSkill = optSkill opts
    }

untilM :: (Monad t) => (t1 -> Bool) -> t t1 -> t t1
untilM t f = f >>= \ y -> if t y then return y else untilM t f

-- should this pre-test?  post-test currently
untilCombM :: (Monad t) => (a -> Bool) -> a -> (a -> t a) -> t a
untilCombM t x f = f x >>= \ y -> if t y then return y else untilCombM t y f

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

eithErr :: (Error e, Monad m) => Either e a -> ErrorT e m a
eithErr = either throwError return

tryRes :: [String] -> Game -> Game
tryRes ls = head $ concatMap tryStr ["0-1", "1-0", "1/2-1/2"] ++ [id] where
  tryStr s = map (\ _ -> setRes $ Just s) $ filter ((s ++ " ") `isPrefixOf`) ls
  setRes res gm = gm {gmRes = res}

compMv :: Game -> ErrorT String IO (String, Game)
compMv gm = do
  pRetLs <- io $ sendForReply gm ["go", "?"]
  let
    moves = filter ("move " `isPrefixOf`) pRetLs
    gm' = tryRes pRetLs gm
  -- fixme: check for more errors?
  when (null moves && isNothing (gmRes gm')) $ throwError "No comp move.."
  when (length moves > 1) $ throwError "Multiple comp moves?"
  case moves of
    [compStr] -> do
      io . debugLog $ "COMPSTR: " ++ compStr
      if "move " `isPrefixOf` compStr
        then do
          let
            'm':'o':'v':'e':' ':compMvStr = compStr
          compMv <- eithErr . resolveMv gm' $ parseMv compMvStr
          gm'' <- eithErr $ doMvPure compMvStr compMv gm'
          return (compMvStr, tryRes pRetLs gm'')
        else throwError "Could not determine computer move."
    _ ->
      -- gmHumans = 2 bc there was no computer move, so this turn must be
      -- considered only as one ply or undo will un-synchronize with engine.
      return ("", gm' {gmHumans = 2})

andLog :: IO String -> IO String
andLog f = do
  y <- f
  debugLog y
  return y

sendForReply :: Game -> [String] -> IO [String]
sendForReply gm ls = do
  let
    Proc pIn pOut pErr pId = gmProc gm
  -- todo: incrementing ping number?
  hPutStr pIn . unlines $ ls ++ ["ping 1"]
  hFlush pIn
  init <$> untilCombM ((== ["pong 1"]) . take 1 . reverse) [] (\ ls -> do
    l <- andLog $ hGetLine pOut
    return $ ls ++ [l])

doMv :: String -> Move -> Game -> ErrorT String IO Game
doMv mvStr mv gm = do
  pRetLs <- io $ sendForReply gm ["force", mvStr]
  -- fixme: check for error
  let
    errs = filter ("Illegal move" `isPrefixOf`) pRetLs
  unless (null errs) . throwError $ head errs
  eithErr $ doMvPure mvStr mv gm

doMvStr :: String -> Game -> ErrorT String IO Game
doMvStr mvStr gm = do
  mv <- eithErr . resolveMv gm $ parseMv mvStr
  doMv mvStr mv gm

saveGm :: Game -> IO ()
saveGm gm = do
  host <- runSL "hostname"
  date <- runSL "date"
  writeFile "game.pgn" . unlines $ [
    "[Event \"-\"]",
    "[Site \"" ++ host ++ "\"]",
    "[Date \"" ++ date ++ "\"]",
    "[Round \"-\"]",
    "[White \"danl\"]",
    "[Black \"crafty skill " ++ show (gmSkill gm) ++ "\"]",
    "[Result \"" ++ fromMaybe "*" (gmRes gm) ++ "\"]",
    "",
    interwords .
    zipWith (\ n l -> show n ++ ". " ++ interwords l) [1..] .
    -- todo?: branching history into pgn
    splitN 2 . PMT.getPath $ gmHist gm]

playGame :: St -> [Game] -> IO ()
playGame st gms = do
  let
    gm = head gms
    noUndo = hPutStrLn stderr "Nothing to undo." >> playGame st gms
    Proc pIn pOut pErr pId = gmProc gm
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
        hPutStrLn pIn $ (if gmHumans gm == 1 then "remove" else "undo")
        hFlush pIn
        saveGm gm
        playGame st $ tail gms
    "2" -> playGame (st {stHumans = 2}) gms
    "1" -> playGame (st {stHumans = 1}) gms
    _ -> do
      clrScr
      ret <- runErrorT $ if stHumans st == 1
        then doMvStr mvStr gm >>= compMv
        else doMvStr mvStr gm >>= \ gm' -> return (mvStr, gm')
      case ret of
        Right (mvStr, gm') -> do
          putStrLn $ mvStr ++ maybe "" (" " ++) (gmRes gm)
          saveGm gm'
          playGame st (gm':gms)
        Left err -> do
          hPutStrLn stderr (show mvStr ++ ": " ++ err)
          playGame st gms

main :: IO ()
main = do
  (opts, args) <- doArgs "usage" defOpts options
  let [] = args
  (pIn, pOut, pErr, pId) <- runInteractiveProcess chProg [] Nothing Nothing
  clrScr
  putStrLn ""
  gm <- initGm opts
  playGame (St 1) [gm]
