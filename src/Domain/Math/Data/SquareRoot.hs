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

module Domain.Math.Data.SquareRoot
   ( SquareRoot
   , imaginary, imaginaryUnit
   , con, toList, scale, fromSquareRoot
   , sqrt, sqrtRational, isqrt, eval
   ) where

import Control.Monad
import Data.Ratio
import Domain.Math.Safe
import Prelude hiding (sqrt)
import Test.QuickCheck hiding (scale)
import qualified Data.Map as M
import qualified Domain.Math.Data.PrimeFactors as P
import qualified Prelude

-------------------------------------------------------------
-- Representation

-- Sum of square roots (possibly imaginary) that are normalized
--
-- Invariants:
-- * all keys are normalized (sqrt 8 -> 2*(sqrt 2))
-- * all values are non-zero
-- * We maintain the "imaginary" property since sqrt(-1)*sqrt(-1) may or may not
--   be equal to sqrt(1)
--
-- Note on the Ord instance: comparison does not follow the value (semantic
-- interpretation); it can be used though for sorting and storing in maps

data SquareRoot a = S
   { imaginary     :: Bool
   , squareRootMap :: SqMap a
   } deriving (Eq, Ord)

type SqMap a = M.Map P.PrimeFactors a

-------------------------------------------------------------
-- Primitive operations on maps

-- re-establish invariants
makeMap :: (Eq a,Num a) => SqMap a -> SqMap a
makeMap = M.filter (/=0) . M.foldrWithKey f M.empty
 where
   f k a m
      | a == 0    = m
      | otherwise = M.unionWith (+) (fmap (*a) (sqrtPF k)) m

plusSqMap :: (Eq a,Num a) => SqMap a -> SqMap a -> SqMap a
plusSqMap m1 m2 = M.filter (/=0) (M.unionWith (+) m1 m2)

minusSqMap :: (Eq a,Num a) => SqMap a -> SqMap a -> SqMap a
minusSqMap m1 m2 = m1 `plusSqMap` negateSqMap m2

negateSqMap :: Num a => SqMap a -> SqMap a
negateSqMap = fmap negate

timesSqMap :: (Eq a,Num a) => SqMap a -> SqMap a -> SqMap a
timesSqMap m1 m2 =
   case (M.toList m1, M.toList m2) of
      ([], _) -> M.empty
      (_, []) -> M.empty
      ([(n, a)], _) | n==1 -> if a==0 then M.empty else fmap (*a) m2
      (_, [(n, a)]) | n==1 -> if a==0 then M.empty else fmap (*a) m1
      _ ->
         let op n a = M.unionWith (+) (f n (fmap (a *) m1))
             f i    = M.mapKeys (*i)
         in makeMap (M.foldrWithKey op M.empty m2)

recipSqMap :: (Eq a,Fractional a) => SqMap a -> SqMap a
recipSqMap m =
   case M.toList m of
      []       -> error "SquareRoot: division by zero"
      [(n, x)] -> M.singleton n (recip (x * fromIntegral n))
      _        -> (a .-. b) .*. recipSqMap (makeMap ((a .*. a) .-. (b .*. b)))
 where
   (ys, zs) = splitAt (length xs `div` 2) xs
   (a, b)   = (M.fromList ys, M.fromList zs)
   xs  = M.toList m
   (.*.) = timesSqMap
   (.-.) = minusSqMap

sqrtPF :: Num a => P.PrimeFactors -> SqMap a
sqrtPF n
   | n == 0    = M.empty
   | otherwise = M.singleton b (fromIntegral a)
 where
   (a, b) = P.splitPower 2 n

-------------------------------------------------------------
-- Type class instances

instance (Show a,Eq a,Num a) => Show (SquareRoot a) where
   show (S isNeg m) = g (map f (M.toList m)) ++ imPart
    where
      f (n, a) = ( signum a == -1
                 , times (guard (abs a /= 1) >> Just (show (abs a)))
                         (guard (n /= 1)     >> Just ("sqrt(" ++ show (toInteger n) ++ ")"))
                 )
      imPart = if isNeg then " (imaginary number)" else ""
      g []         = "0"
      g ((b,x):xs) = (if b then "-" else "") ++ x ++ concatMap h xs
      h (b, x)     = (if b then " - " else " + ") ++ x

      times (Just a) (Just b) = a ++ "*" ++ b
      times (Just a) Nothing  = a
      times Nothing  (Just b) = b
      times Nothing  Nothing  = "1"

-- the Functor instance does not maintain the invariant (non-zero)
instance Functor SquareRoot where
   fmap f (S b m) = S b (M.map f m)

instance (Eq a,Num a) => Num (SquareRoot a) where
   S b1 m1 + S b2 m2 = S (b1 || b2) (plusSqMap  m1 m2)
   S b1 m1 - S b2 m2 = S (b1 || b2) (minusSqMap m1 m2)
   S b1 m1 * S b2 m2 = S (b1 || b2) (timesSqMap m1 m2)
   negate (S b m)    = S b (negateSqMap m)
   fromInteger       = con . fromInteger

   -- not defined for square roots
   abs    = error "abs not defined for square roots"
   signum = error "signum not defined for square roots"

instance (Eq a,Fractional a) => SafeDiv (SquareRoot a) where
   safeDiv x y
      | y == 0    = Nothing
      | otherwise = Just (x/y)

instance (Eq a,Fractional a) => Fractional (SquareRoot a) where
   recip (S b m) = S b (recipSqMap m)
   fromRational  = con . fromRational

instance (Eq a,Fractional a) => Arbitrary (SquareRoot a) where
   arbitrary = sized $ \n -> do
      let make r1 r2 = fromRational r1 * sqrtRational r2
      i <- choose (0, 10)
      xs <- vectorOf i (liftM2 make (rationalGen n) (rationalGen n))
      return (sum xs)

rationalGen :: Int -> Gen Rational
rationalGen n = do -- a+(b/c)
   c <- choose (0, n)
   b <- choose (0, c)
   a <- choose (0, n)
   return $ fromIntegral a + if c==0 then 0
                                     else fromIntegral b / fromIntegral c

-------------------------------------------------------------
-- Utility functions

imaginaryUnit :: Num a => SquareRoot a
imaginaryUnit = S True (M.singleton (-1) 1)

toList :: SquareRoot a -> [(a, Integer)]
toList = map (\(k, r) -> (r, toInteger k)) . M.toList . squareRootMap

fromSquareRoot :: Num a => SquareRoot a -> Maybe a
fromSquareRoot a =
   case toList a of
      [(b, n)] | n==1 -> Just b
      []              -> Just 0
      _ -> Nothing

con :: (Eq a,Num a) => a -> SquareRoot a
con a = S False (if a==0 then M.empty else M.singleton 1 a)

sqrt :: Num a => Integer -> SquareRoot a
sqrt n
   | n < 0     = S True (M.mapKeys negate m)
   | otherwise = S False m
 where
   m = sqrtPF (fromIntegral (abs n))

scale :: (Eq a,Num a) => a -> SquareRoot a -> SquareRoot a
scale a sr = if a==0 then 0 else fmap (*a) sr

isqrt :: Integer -> Integer
isqrt = (floor :: Double -> Integer) . Prelude.sqrt . fromInteger

sqrtRational :: (Eq a,Fractional a) => Rational -> SquareRoot a
sqrtRational r = scale (1/fromIntegral b) (sqrt (a*b))
 where
   (a, b) = (numerator r, denominator r)

eval :: Floating a => SquareRoot a -> a
eval (S _ m) = M.foldrWithKey f 0 m
 where f n a b = a * Prelude.sqrt (fromIntegral n) + b