{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test where

import Data.Char
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

chkPawn :: Col -> PawnDestRow -> Bool
chkPawn c r = gmBd (doMv [unCol c, unPawnDestRow r] initGm) /= gmBd initGm

qc = verboseCheck chkPawn
