{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
-- Copyright 2019, Ideas project team. This file is distributed under the
-- terms of the Apache License 2.0. For more information, see the files
-- "LICENSE.txt" and "NOTICE.txt", which are included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-----------------------------------------------------------------------------

module Domain.Logic.Generator
   ( generateLogic, generateLevel, equalLogicA, equalLogicACI,equalLogicAC
   , normalizeLogicA
   ) where

import Control.Monad
import Data.Char
import Data.Function
import Data.List
import Domain.Logic.Formula
import Ideas.Common.Exercise
import Ideas.Utils.Prelude (ShowString(..))
import Ideas.Utils.Uniplate
import Test.QuickCheck

-------------------------------------------------------------
-- Code that doesn't belong here

-- | Equality modulo associativity of operators
equalLogicA :: Eq a => Logic a -> Logic a -> Bool
equalLogicA = (==) `on` normalizeLogicA

normalizeLogicA :: Logic a -> Logic a
normalizeLogicA a =
   case a of
      _ :&&: _ -> ands (map normalizeLogicA (conjunctions a))
      _ :||: _ -> ors  (map normalizeLogicA (disjunctions a))
      _        -> descend normalizeLogicA a

-- | Equality modulo associativity/commutativity/idempotency of operators,
--   and there units/absorbing elements
equalLogicACI :: Ord a => Logic a -> Logic a -> Bool
equalLogicACI p q = rec p == rec q
 where
   rec a@(_ :&&: _) =
      let xs = filter (/=T) $ nub $ sort $ conjunctions a
      in if F `elem` xs then F else ands (map rec xs)
   rec a@(_ :||: _) =
      let xs = filter (/=F) $ nub $ sort $ disjunctions a
      in if T `elem` xs then T else ors (map rec xs)
   rec a = descend rec a

   -- | Equality modulo associativity/commutativity
equalLogicAC :: Ord a => Logic a -> Logic a -> Bool
equalLogicAC p q = rec p == rec q
 where
   rec a@(_ :&&: _) =
      let xs = sort $ conjunctions a
      in ands (map rec xs)
   rec a@(_ :||: _) =
      let xs = sort $ disjunctions a
      in ors (map rec xs)
   rec a = descend rec a

-----------------------------------------------------------
-- Logic generator

generateLogic :: Gen SLogic
generateLogic = normalGenerator

generateLevel :: Difficulty -> (Gen SLogic, (Int, Int))
generateLevel dif
   | dif <= Easy      = (easyGenerator,      (3, 6))
   | dif >= Difficult = (difficultGenerator, (7, 18))
   | otherwise        = (normalGenerator,    (4, 12))

-- Use the propositions with 3-6 steps
easyGenerator :: Gen SLogic
easyGenerator = do
   n  <- elements [2, 4] -- , return 8]
   sizedGen True varGen n

-- Use the propositions with 4-12 steps
normalGenerator :: Gen SLogic
normalGenerator = do
   p0 <- sizedGen False varGen 4
   p1 <- preventSameVar varList p0
   return (removePartsInDNF p1)

-- Use the propositions with 7-18 steps
difficultGenerator :: Gen SLogic
difficultGenerator = do
   let vs = ShowString "s" : varList
   p0 <- sizedGen False (elements vs) 4
   p1 <- preventSameVar vs p0
   return (removePartsInDNF p1)

varList :: [ShowString]
varList = map ShowString ["p", "q", "r"]

varGen :: Gen ShowString
varGen = elements varList

sizedGen :: Bool -> Gen a -> Int -> Gen (Logic a)
sizedGen constants gen = go
 where
   go n
      | n > 0 =
           let rec   = go (n `div` 2)
               op2 f = liftM2 f rec rec
           in frequency
                 [ (2, go 0)
                 , (2, op2 (:->:))
                 , (1, op2 (:<->:))
                 , (3, op2 (:&&:))
                 , (3, op2 (:||:))
                 , (3, liftM Not rec)
                 ]
      | constants = frequency
           [(5, liftM Var gen), (1, return T), (1, return F)]
      | otherwise = liftM Var gen

-----------------------------------------------------------------
-- Simple tricks for creating for "nice" logic propositions

preventSameVar :: Eq a => [a] -> Logic a -> Gen (Logic a)
preventSameVar xs = rec
 where
   rec p = case holes p of
              [(Var a, _), (Var b, update)] | a==b -> do
                 c <- elements $ filter (/=a) xs
                 return $ update (Var c)
              _ -> descendM rec p

removePartsInDNF :: SLogic -> SLogic
removePartsInDNF = buildOr . filter (not . simple) . disjunctions
 where
   buildOr [] = T
   buildOr xs = foldl1 (:||:) xs

   simple = all f . conjunctions
    where
      f (Not p) = null (children p)
      f p       = null (children p)

-----------------------------------------------------------
--- QuickCheck generator

instance Arbitrary SLogic where
   arbitrary = sized (\i -> sizedGen True varGen (i `min` 4))

instance CoArbitrary SLogic where
   coarbitrary = foldLogic
      (var, bin 1, bin 2, bin 3, bin 4, un 5, con 6, con 7)
    where
      con       = variant :: Int -> Gen a -> Gen a
      var       = un 0 . coarbitrary . map ord . fromShowString
      un  n a   = con n . a
      bin n a b = con n . a . b