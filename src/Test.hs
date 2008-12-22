{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test where

import Data.Char
import Data.Maybe
import System.Random
import Test.QuickCheck

import Main

newtype PawnDestRow = PawnDestRow {unPawnDestRow :: Char} deriving
  (Random, Show)
newtype Col = Col {unCol :: Char} deriving (Random, Show)

instance Arbitrary PawnDestRow where
  arbitrary = choose (PawnDestRow '3', PawnDestRow '4')
  coarbitrary c = variant . ord $ unPawnDestRow c

instance Arbitrary Col where
  arbitrary = choose (Col 'a', Col 'h')
  coarbitrary c = variant . ord $ unCol c

chkPawn :: Game -> Col -> PawnDestRow -> Bool
chkPawn gm c r = either (const False) id $ do
  gm' <- doMvStrPure [unCol c, unPawnDestRow r] gm
  return $ gmBd gm' /= gmBd gm

runTests = do
  gm <- initGm
  verboseCheck $ chkPawn gm
