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

module Domain.Math.Data.MixedFraction
   ( MixedFraction, wholeNumber, fractionPart, numerator, denominator
   ) where

import qualified Data.Ratio as R

newtype MixedFraction = MF { unMF :: Rational }
   deriving (Eq, Ord, Num, Fractional, Real, RealFrac)

instance Show MixedFraction where
   show mf
      | b == 0    = sign ++ show a
      | a == 0    = sign ++ show b ++ "/" ++ show c
      | otherwise = sign ++ show a ++ "[" ++ show b ++ "/" ++ show c ++ "]"
    where
      (a, b, c) = (wholeNumber mf, numerator mf, denominator mf)
      sign = if mf < 0 then "-" else ""

-- | Always positive
wholeNumber :: MixedFraction -> Integer
wholeNumber = fst . properMF

-- | Always positive
fractionPart :: MixedFraction -> Rational
fractionPart = snd . properMF

-- | Always positive
numerator :: MixedFraction -> Integer
numerator = R.numerator . fractionPart

-- | Always positive
denominator :: MixedFraction -> Integer
denominator = R.denominator . fractionPart

-- local helper
properMF :: MixedFraction -> (Integer, Rational)
properMF = properFraction . abs . unMF