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
-- Exports relevant OpenMath symbols
--
-----------------------------------------------------------------------------

module Domain.Math.Expr.Symbols
   ( -- OpenMath dictionary symbols
     plusSymbol, timesSymbol, minusSymbol, divideSymbol, rationalSymbol
   , rootSymbol, gcdSymbol, lcmSymbol
   , powerSymbol, negateSymbol, sinSymbol, cosSymbol, lnSymbol
   , diffSymbol, piSymbol, lambdaSymbol, listSymbol
   , absSymbol, signumSymbol, logSymbol, expSymbol, tanSymbol, asinSymbol
   , atanSymbol, acosSymbol, sinhSymbol, tanhSymbol, coshSymbol, asinhSymbol
   , atanhSymbol, acoshSymbol, bottomSymbol, fcompSymbol, mixedFractionSymbol
     -- Matching
   , isPlus, isTimes, isMinus, isDivide, isPower, isNegate, isRoot
   , isPowerSymbol, isRootSymbol, isLogSymbol, isDivideSymbol
   , isMixedFractionSymbol
   , (^), root, mixed
   ) where

import Ideas.Common.Rewriting
import Prelude hiding ((^))
import qualified Ideas.Text.OpenMath.Dictionary.Arith1 as OM
import qualified Ideas.Text.OpenMath.Dictionary.Calculus1 as OM
import qualified Ideas.Text.OpenMath.Dictionary.Fns1 as OM
import qualified Ideas.Text.OpenMath.Dictionary.List1 as OM
import qualified Ideas.Text.OpenMath.Dictionary.Nums1 as OM
import qualified Ideas.Text.OpenMath.Dictionary.Transc1 as OM

-------------------------------------------------------------
-- Arith1 dictionary

plusSymbol, timesSymbol, minusSymbol, divideSymbol, rootSymbol,
   powerSymbol, negateSymbol, absSymbol, gcdSymbol, lcmSymbol :: Symbol

plusSymbol     = newSymbol OM.plusSymbol
timesSymbol    = newSymbol OM.timesSymbol
minusSymbol    = newSymbol OM.minusSymbol
divideSymbol   = newSymbol OM.divideSymbol
rootSymbol     = newSymbol OM.rootSymbol
powerSymbol    = newSymbol OM.powerSymbol
negateSymbol   = newSymbol OM.unaryMinusSymbol
absSymbol      = newSymbol OM.absSymbol
gcdSymbol      = newSymbol OM.gcdSymbol
lcmSymbol      = newSymbol OM.lcmSymbol

-------------------------------------------------------------
-- Transc1 dictionary

logSymbol, sinSymbol, cosSymbol, lnSymbol, expSymbol, tanSymbol,
   sinhSymbol, tanhSymbol, coshSymbol :: Symbol

logSymbol  = newSymbol OM.logSymbol
sinSymbol  = newSymbol OM.sinSymbol
cosSymbol  = newSymbol OM.cosSymbol
lnSymbol   = newSymbol OM.lnSymbol
expSymbol  = newSymbol OM.expSymbol
tanSymbol  = newSymbol OM.tanSymbol
sinhSymbol = newSymbol OM.sinhSymbol
tanhSymbol = newSymbol OM.tanhSymbol
coshSymbol = newSymbol OM.coshSymbol

-------------------------------------------------------------
-- Other dictionaries

diffSymbol, lambdaSymbol, listSymbol, piSymbol, rationalSymbol :: Symbol

diffSymbol     = newSymbol OM.diffSymbol
lambdaSymbol   = newSymbol OM.lambdaSymbol
listSymbol     = newSymbol OM.listSymbol
piSymbol       = newSymbol OM.piSymbol
rationalSymbol = newSymbol OM.rationalSymbol

-------------------------------------------------------------
-- Extra math symbols

signumSymbol, asinSymbol, atanSymbol, acosSymbol, asinhSymbol, atanhSymbol,
   acoshSymbol, bottomSymbol, fcompSymbol, mixedFractionSymbol :: Symbol

signumSymbol = newSymbol "signum"
asinSymbol   = newSymbol "asin"
atanSymbol   = newSymbol "atan"
acosSymbol   = newSymbol "acos"
asinhSymbol  = newSymbol "asinh"
atanhSymbol  = newSymbol "atanh"
acoshSymbol  = newSymbol "acosh"
bottomSymbol = newSymbol "error"
fcompSymbol  = newSymbol "compose"

-- support for mixed fractions
mixedFractionSymbol = newSymbol ("extra", "mixedfraction")

-------------------------------------------------------------
-- Some match functions

isPlus, isTimes, isMinus, isDivide, isPower, isRoot ::
   WithFunctions a => a -> Maybe (a, a)
isNegate :: WithFunctions a => a -> Maybe a

isPlus   = isAssoBinary plusSymbol
isTimes  = isAssoBinary timesSymbol
isMinus  = isBinary     minusSymbol
isDivide = isBinary     divideSymbol
isNegate = isUnary      negateSymbol
isPower  = isBinary     powerSymbol
isRoot   = isBinary     rootSymbol

isPowerSymbol, isRootSymbol, isLogSymbol, isDivideSymbol,
   isMixedFractionSymbol :: Symbol -> Bool

isPowerSymbol  = (== powerSymbol)
isRootSymbol   = (== rootSymbol)
isLogSymbol    = (== logSymbol)
isDivideSymbol = (== divideSymbol)

isMixedFractionSymbol = (== mixedFractionSymbol)

infixr 8 ^

(^) :: WithFunctions a => a -> a -> a
(^) = binary powerSymbol

root :: WithFunctions a => a -> a -> a
root = binary rootSymbol

mixed :: (Num a, WithFunctions a) => Integer -> Integer -> Integer -> a
mixed a b c = function mixedFractionSymbol $ map fromInteger [a, b, c]

-------------------------------------------------------------
-- Helper

-- left-associative
isAssoBinary :: WithFunctions a => Symbol -> a -> Maybe (a, a)
isAssoBinary s a =
   case isFunction s a of
      Just [x, y] -> Just (x, y)
      Just (x:xs) | length xs > 1 -> Just (x, function s xs)
      _ -> Nothing