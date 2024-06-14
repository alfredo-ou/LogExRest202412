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

module Domain.Math.Safe
   ( -- * Safe division
     SafeDiv(..), safeDivFractional
   , -- * Safe power and root
     SafePower(..)
   ) where

import Control.Monad
import Data.Ratio

-------------------------------------------------------------------
-- Safe division

class Num a => SafeDiv a where
   safeDiv   :: a -> a -> Maybe a
   safeRecip :: a -> Maybe a
   -- default definitions
   safeRecip = safeDiv 1

instance SafeDiv Integer where
   safeDiv x y
      | y /= 0 && m == 0 = Just d
      | otherwise        = Nothing
    where (d, m) = x `divMod` y

instance SafeDiv Double where
   safeDiv = safeDivFractional

instance Integral a => SafeDiv (Ratio a) where
   safeDiv = safeDivFractional

safeDivFractional :: (Eq a,Fractional a) => a -> a -> Maybe a
safeDivFractional x y
   | y /= 0    = Just (x / y)
   | otherwise = Nothing

-------------------------------------------------------------------
-- Safe power and root

class Num a => SafePower a where
   safePower :: a -> a -> Maybe a
   safeSqrt  :: a -> Maybe a
   safeRoot  :: a -> a -> Maybe a
   -- default definitions
   safeSqrt = (`safeRoot` 2)

instance SafePower Integer where
   safeRoot x y =
      case fmap round (safeRoot (fromInteger x :: Double) (fromInteger y)) of
         Just a | safePower a y == Just x -> Just a
         _ -> Nothing
   safePower x y
      | y >= 0    = Just (x ^ y)
      | otherwise = Nothing

instance Integral a => SafePower (Ratio a) where
   safeRoot x y = do
      let n = toInteger (numerator y)
      guard (denominator y == 1)
      a <- safeRoot (toInteger (numerator x)) n
      b <- safeRoot (toInteger (denominator x)) n
      safeDiv (fromInteger a) (fromInteger b)
   safePower x y
      | denominator y /= 1 = Nothing
      | numerator y >= 0   = Just a
      | otherwise          = Just (1/a)
    where
      a = x ^ abs (numerator y)

instance SafePower Double where
   safePower x y
      | x==0 && y<0 = Nothing
      | otherwise   = Just (x**y)
   safeRoot x y
      | x >= 0 && y >= 1 = Just (x ** (1/y))
      | otherwise        = Nothing