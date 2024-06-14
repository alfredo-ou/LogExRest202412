{-# LANGUAGE DeriveDataTypeable #-}
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

module Domain.Math.Expr.Data
   ( Expr(..), toExpr, fromExpr, fromDouble
   ) where

import Control.Applicative
import Control.Monad
import Data.Char (isAlphaNum)
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Typeable
import Domain.Logic.Formula hiding (Var)
import Domain.Math.Data.Relation (relationSymbols)
import Domain.Math.Expr.Symbols
import Ideas.Common.Rewriting hiding (trueSymbol, falseSymbol)
import Ideas.Utils.Uniplate
import Test.QuickCheck hiding (function)
import qualified Domain.Algebra.Field as F

-----------------------------------------------------------------------
-- Expression data type

data Expr = -- Num
            Expr :+: Expr
          | Expr :*: Expr
          | Expr :-: Expr
          | Negate Expr
          | Nat Integer
            -- Fractional
          | Expr :/: Expr
            -- Floating-point
          | Sqrt Expr
          | Number Double -- positive only
            -- Symbolic
          | Var String
          | Sym Symbol [Expr]
   deriving (Eq, Ord, Typeable)

-----------------------------------------------------------------------
-- Numeric instances (and symbolic)

instance Num Expr where
   (+) = (:+:)
   (*) = (:*:)
   (-) = (:-:)
   fromInteger n
      | n < 0     = negate $ Nat $ abs n
      | otherwise = Nat n
   negate = Negate
   abs    = unary absSymbol
   signum = unary signumSymbol

instance Fractional Expr where
   (/) = (:/:)
   fromRational r
      | denominator r == 1 =
           fromIntegral (numerator r)
      | numerator r < 0 =
           Negate (fromIntegral (abs (numerator r)) :/: fromIntegral (denominator r))
      | otherwise =
           fromIntegral (numerator r) :/: fromIntegral (denominator r)

instance Floating Expr where
   pi      = symbol piSymbol
   sqrt    = Sqrt
   (**)    = binary powerSymbol
   logBase = binary logSymbol
   exp     = unary expSymbol
   log     = unary logSymbol
   sin     = unary sinSymbol
   tan     = unary tanSymbol
   cos     = unary cosSymbol
   asin    = unary asinSymbol
   atan    = unary atanSymbol
   acos    = unary acosSymbol
   sinh    = unary sinhSymbol
   tanh    = unary tanhSymbol
   cosh    = unary coshSymbol
   asinh   = unary asinhSymbol
   atanh   = unary atanhSymbol
   acosh   = unary acoshSymbol

instance WithFunctions Expr where
   function s (a:as) -- make binary
      | s == plusSymbol   = foldl (:+:) a as
      | s == timesSymbol  = foldl (:*:) a as
   function s [a, b]
      | s == minusSymbol    = a :-: b
      | s == divideSymbol   = a :/: b
      | s == rationalSymbol = a :/: b
      | s == mixedFractionBinarySymbol = a :+: b
      | isRootSymbol s && b == Nat 2 || b == Number 2.0 = Sqrt a
   function s [a]
      | s == negateSymbol = Negate a
   function s as = Sym s as

   getFunction expr =
      case expr of
         a :+: b  -> return (plusSymbol,   [a, b])
         a :*: b  -> return (timesSymbol,  [a, b])
         a :-: b  -> return (minusSymbol,  [a, b])
         Negate a -> return (negateSymbol, [a])
         a :/: b  -> return (divideSymbol, [a, b])
         Sqrt a   -> return (rootSymbol,   [a, Nat 2])
         Sym s as -> return (s, as)
         _ -> fail "Expr.getFunction"

-- Special symbol in Math-Bridge/ActiveMath
mixedFractionBinarySymbol :: Symbol
mixedFractionBinarySymbol = newSymbol "elementary.mixed_fraction"

instance WithVars Expr where
   variable = Var
   getVariable (Var s) = return s
   getVariable _       = fail "Expr.getVariable"

fromDouble :: Double -> Expr
fromDouble d
   | d < 0     = negate (Number (abs d))
   | otherwise = Number d

-----------------------------------------------------------------------
-- Uniplate instance

instance Uniplate Expr where
   uniplate expr =
      case getFunction expr of
         Just (s, as) -> plate function |- s ||* as
         _            -> plate expr

-----------------------------------------------------------------------
-- Arbitrary instance

instance Arbitrary Expr where
   arbitrary = fromInteger <$> arbitrary
      -- before changing this instance, check that the
      -- Gaussian elimination exercise still works (with checkExercise)
      {-
      let syms = [plusSymbol, timesSymbol, minusSymbol, negateSymbol, divSymbol]
      in sized (symbolGenerator (const [natGenerator]) syms) -}

-----------------------------------------------------------------------
-- Pretty printer

instance Show Expr where
   show = showExpr operatorTable

showExpr :: OperatorTable -> Expr -> String
showExpr table = rec 0
 where
   rec :: Int -> Expr -> String
   rec _ (Nat n)    = if n>=0 then show n else "(ERROR)" ++ show n
   rec _ (Number d) = if d>=0 then show d else "(ERROR)" ++ show d
   rec _ (Var s)
      | all isAlphaNum s = s
      | otherwise        = "\"" ++ s ++ "\""
   rec i expr =
      case getFunction expr of
         Just (s1, [Sym s2 [Var x, a]]) | s1 == diffSymbol && s2 == lambdaSymbol ->
            parIf (i>10000) $ "D(" ++ x ++ ") " ++ rec 10001 a
         Just (s, [Nat a, Nat b, Nat c]) | s == mixedFractionSymbol ->
            let ok  = all (>= 0) [a, b, c]
                err = if ok then "" else "(ERROR)"
            in err ++ show a ++ "[" ++ show b ++ "/" ++ show c ++ "]"
         -- To do: remove special case for sqrt
         Just (s, [a, b]) | isRootSymbol s && b == Nat 2 ->
            parIf (i>10000) $ unwords ["sqrt", rec 10001 a]
         Just (s, xs) | s == listSymbol ->
            "[" ++ intercalate ", " (map (rec 0) xs) ++ "]"
         Just (s, []) | s == trueSymbol  -> "T"
                      | s == falseSymbol -> "F"
         Just (s, as) ->
            case (lookup s symbolTable, as) of
               (Just (InfixLeft, n, op), [x, y]) ->
                  parIf (i>n) $ rec n x ++ op ++ rec (n+1) y
               (Just (InfixRight, n, op), [x, y]) ->
                  parIf (i>n) $ rec (n+1) x ++ op ++ rec n y
               (Just (InfixNon, n, op), [x, y]) ->
                  parIf (i>n) $ rec (n+1) x ++ op ++ rec (n+1) y
               (Just (PrefixNon, n, op), [x]) ->
                  parIf (i>=n) $ op ++ rec (n+1) x
               _ ->
                  parIf (not (null as) && i>10000) $ unwords (showSymbol s : map (rec 10001) as)
         Nothing ->
            error "showExpr"

   showSymbol s
      | isRootSymbol s = "root"
      | isLogSymbol s  = "log"
      | s == sinSymbol = "sin"
      | s == cosSymbol = "cos"
      | s == piSymbol  = "pi"
      | otherwise = show s

   symbolTable = [ (s, (a, n, op)) | (n, (a, xs)) <- zip [1..] table, (s, op) <- xs ]

   parIf b = if b then par else id
   par s   = "(" ++ s ++ ")"

type OperatorTable = [(Associativity, [(Symbol, String)])]

data Associativity = InfixLeft | InfixRight | PrefixNon
                   | InfixNon
   deriving (Show, Eq)

operatorTable :: OperatorTable
operatorTable =
   -- relation operators
     (InfixNon, [ (s, space op) | (_, (op, s)) <- relationSymbols]) :
   -- logic operators
   [ (InfixNon,   [(impliesSymbol, "->"), (equivalentSymbol, "<->")]) -- 1
   , (InfixRight, [(orSymbol, "||")])                         -- 2
   , (InfixRight, [(andSymbol, "&&")])                        -- 3
   , (PrefixNon,  [(notSymbol, "~")])                         -- 4
   -- arithmetic operators
   , (InfixLeft,  [(plusSymbol, "+"), (minusSymbol, "-")])    -- 6
   , (PrefixNon,  [(negateSymbol, "-")])                      -- 6+
   , (InfixLeft,  [(timesSymbol, "*"), (divideSymbol, "/")])  -- 7
   , (InfixRight, [(powerSymbol, "^")])                       -- 8
   ]
 where
   space a = " " ++ a ++ " " -- for consistency with Show Equation

instance BoolValue Expr where
   true  = Sym trueSymbol []
   false = Sym falseSymbol []

   isTrue (Sym s []) = s == trueSymbol
   isTrue _          = False

   isFalse (Sym s []) = s == falseSymbol
   isFalse _          = False

instance Boolean Expr where
   complement p = Sym notSymbol [p]
   p <&&> q = Sym andSymbol [p, q]
   p <||> q = Sym orSymbol [p, q]

instance CoBoolean Expr where
   isAnd (Sym s [p, q]) | s == andSymbol = Just (p, q)
   isAnd _ = Nothing
   isOr (Sym s [p, q]) | s == orSymbol = Just (p, q)
   isOr _ = Nothing
   isComplement (Sym s [p]) | s == notSymbol = Just p
   isComplement _ = Nothing

instance F.SemiRing Expr where
   (|+|) = (+)
   zero  = 0
   (|*|) = (*)
   one   = 1

instance F.Ring Expr where
   plusInverse = negate
   (|-|)       = (-)

instance F.Field Expr where
   timesInverse = recip
   (|/|)        = (/)

instance F.CoSemiRing Expr where
   isPlus  = isPlus
   isZero  = (==0)
   isTimes = isTimes
   isOne   = (==1)

instance F.CoRing Expr where
   isNegate = isNegate
   isMinus  = isMinus

instance F.CoField Expr where
   isRecip _  = Nothing
   isDivision = isDivide

instance Different Expr where
   different = (Nat 0, Nat 1)

instance IsTerm Expr where
   toTerm (Nat n)    = TNum n
   toTerm (Number d) = TFloat d
   toTerm (Var v)    = TVar v
   toTerm expr =
      case getFunction expr of
         Just (s, xs)
            | s == listSymbol -> TList (map toTerm xs)
            | otherwise       -> function s (map toTerm xs)
         Nothing      -> error "IsTerm Expr"

   termDecoder
       =  fromInteger <$> tInteger
      <|> fromDouble <$> tDouble
      <|> Var <$> tVar
      <|> function listSymbol <$> tListOf termDecoder
      <|> tConWithSymbol function termDecoder

toExpr :: IsTerm a => a -> Expr
toExpr = fromJust . fromTerm . toTerm

fromExpr :: IsTerm a => Expr -> Maybe a
fromExpr = fromTerm . toTerm