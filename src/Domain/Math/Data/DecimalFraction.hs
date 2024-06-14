{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

module Domain.Math.Data.DecimalFraction
   ( DecimalFraction(..), fromDouble, validDivisor, digits
   ) where

import Control.Monad
import Data.Maybe
import Data.Ratio
import Domain.Math.Safe

import Test.QuickCheck

-- |Data type for decimal fractions
newtype DecimalFraction = DF Rational -- Invariant: denominator is valid
   deriving (Eq, Ord, Num, Real, Arbitrary)

instance Show DecimalFraction where
   show d@(DF r) = show x ++ "." ++ replicate extra '0' ++ show y
    where
      digs   = digits d
      base   = 10^digs
      n      = numerator (r * fromInteger base)
      (x, y) = n `divMod` base
      extra  = digs - length (show y)

instance Fractional DecimalFraction where
   a/b = fromMaybe (error "invalid divisor") (safeDiv a b)
   fromRational r = fromInteger (numerator r) / fromInteger (denominator r)

instance SafeDiv DecimalFraction where
   safeDiv (DF a) (DF b) = do
      guard (validDivisor (DF b))
      fmap DF (a `safeDiv` b)

instance SafePower DecimalFraction where
   safePower x (DF r)
      | denominator r /= 1 = Nothing
      | y >= 0             = Just a
      | otherwise          = safeDiv 1 a
    where
      y = numerator r
      a = x Prelude.^ abs y
   safeRoot x y = safeRecip y >>= safePower x

-- | Approximation of a double, with a precision of 8 digits
fromDouble :: Double -> DecimalFraction
fromDouble d = DF (fromInteger base / 10^digs)
 where
   digs = 8 :: Int -- maximum number of digits
   base = round (d * 10^digs) :: Integer

-- |Tests whether it is safe to divide by this fraction: it is safe to divide
-- if its numerator(!) is a product of two's and five's.
validDivisor :: DecimalFraction -> Bool
validDivisor (DF a) = validDenominator (abs (numerator a))

-- |number of decimal digits
digits :: DecimalFraction -> Int
digits (DF r) = head $ filter p [0..]
 where
   p i = 10^i `mod` denominator r == 0

-- local helper
validDenominator :: Integer -> Bool
validDenominator n
   | n == 0         = False
   | even n         = validDenominator (n `div` 2)
   | n `mod` 5 == 0 = validDenominator (n `div` 5)
   | otherwise      = n == 1