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

module Domain.Math.Data.PrimeFactors
   ( PrimeFactors
   , splitPower, greatestPower, allPowers
   ) where

import Data.Maybe
import Domain.Math.Data.Primes
import qualified Data.IntMap as IM

-------------------------------------------------------------
-- Representation

-- Invariants:
-- * Keys in map are prime numbers only (exception: representation of 0)
-- * Elements in map are positive (non-zero)
-- * Zero is represented by [(0,1)] (since 0^1 equals 0)
-- * The number can be negative, in which case we use the factors of
--   its absolute value
data PrimeFactors = PF Integer Factors

type Factors = IM.IntMap Int

-------------------------------------------------------------
-- Conversion to and from factors

toFactors :: Integer -> Factors
toFactors a
   | a == 0    = IM.singleton 0 1
   | otherwise = rec $ primeFactors $ abs $ fromInteger a
 where
   rec []     = IM.empty
   rec (x:xs) = IM.insert x (length ys + 1) (rec zs)
    where
      (ys, zs) = break (/= x) xs

fromFactors :: Factors -> Integer
fromFactors = product . map f . IM.toList
 where f (a, i) = toInteger a ^ toInteger i

-------------------------------------------------------------
-- Type class instances

instance Show PrimeFactors where
   show (PF a m) = show a ++ " (factors = " ++ show (IM.toList m) ++ ")"

instance Eq PrimeFactors where
    PF a _ == PF b _ = a==b

instance Ord PrimeFactors where
   PF a _ `compare` PF b _ = a `compare` b

instance Num PrimeFactors where
   PF a m1 + PF b m2
      | a==0         = PF b m2 -- prevent recomputing prime factors
      | b==0         = PF a m1
      | otherwise    = fromInteger (a+b)
   PF a m1 * PF b m2
      | a==0 || b==0 = 0
      | otherwise    = PF (a*b) (IM.unionWith (+) m1 m2)
   negate (PF a m)   = PF (negate a) m
   abs    (PF a m)   = PF (abs a) m
   signum (PF a _)   = fromInteger (signum a)
   fromInteger n     = PF n (toFactors n)

instance Enum PrimeFactors where
   toEnum   = fromIntegral
   fromEnum = fromIntegral . toInteger

instance Real PrimeFactors where
   toRational = toRational . toInteger

instance Integral PrimeFactors where
   toInteger (PF a _) = a
   quotRem = quotRemPF

-------------------------------------------------------------
-- Utility functions

-- brute force, ugly
greatestPower :: Integer -> Maybe (Integer, Integer)
greatestPower n = f 2 1
  where
    f b e | n == b ^ e = Just (b, e)
          | b > n      = Nothing
          | b ^ e > n  = f (b + 1) 1
          | otherwise  = f b (e + 1)

-- -- n == a^x with (a,x) == greatestPower n
-- prop_greatestPower n = traceShow n $
--    maybe True (\(a,x) -> fromIntegral a ^ fromIntegral x == n) $ greatestPower n

allPowers :: Integer -> [(Integer, Integer)]
allPowers n = do
  (b, e) <- maybeToList $ greatestPower n
  let f i = let (a, r) = e `divMod` i
            in if a > 1 && r == 0 then Just (b^i, a) else Nothing
  mapMaybe f [1..e]

-- prop_allPowers n = traceShow n $
--   and (map (\(a,x) -> fromIntegral a ^ fromIntegral x == n) (allPowers n))

-- splitPower i a = (b,c)
--  => b^i * c = a
splitPower :: Int -> PrimeFactors -> (PrimeFactors, PrimeFactors)
splitPower i (PF a m) = (PF b p1, PF c p2)
 where
   pairs = IM.map (`quotRem` i) m
   p1    = IM.filter (>0) (fmap fst pairs)
   p2    = IM.filter (>0) (fmap snd pairs)
   b     = fromFactors p1
   c     = a `div` (b^i)

quotRemPF :: PrimeFactors -> PrimeFactors -> (PrimeFactors, PrimeFactors)
quotRemPF (PF a m1) (PF b m2)
   | b==0 = error "PrimeFactors: division by zero"
   | a==0 = (0,0)
   | otherwise = sign $
        case (IM.null up, IM.null dn) of
           (True,  True)  -> (1, 0)
           (False, True)  -> (PF (fromFactors up) up, 0)
           (True,  False) -> (0, PF a m1)
           _              -> (fromInteger qn, fromInteger rn)
 where
   (up, dn) = IM.partition (>0) $ IM.filter (/=0) $ IM.unionWith (+) m1 (IM.map negate m2)
   (qn, rn) = fromFactors up `quotRem` fromFactors (IM.map negate dn)
   sign (q, r) = ( fromInteger (signum a*signum b) * q
                 , fromInteger (signum a) * r
                 )