module Domain.Logic.Inductive.ExprUtils 
   ( similarExpr, unionAssoView
   , lessExpr, leqExpr
   , checkUnionACI
   ) where

import Control.Monad
import Ideas.Common.View
import Ideas.Common.Classes
import qualified Data.Set as S
import Data.Maybe
import Domain.Math.Numeric.Views
import Domain.Math.Expr
import Domain.Logic.Inductive.Symbols

similarExpr :: Expr -> Expr -> Bool
similarExpr x y =
   case (match naturalView x, match naturalView y) of
      (Just i, Just j) -> i == j
      _ | xs /= xs2 -> similarExpr (build sumView xs2) (build sumView ys2)
       where (xs2, ys2) = removeSame (map commMinMax xs) (map commMinMax ys)
      _ | length setx > 1 && similarExprs setx sety -> True
        | otherwise -> 
         case (x, y) of 
            (x1 :+: x2, y1 :+: y2)   -> similarExprs [x1, x2] [y1, y2]
            (x1 :*: x2, y1 :*: y2)   -> similarExprs [x1, x2] [y1, y2]
            (x1 :-: x2, y1 :-: y2)   -> similarExprs [x1, x2] [y1, y2]
            (x1 :/: x2, y1 :/: y2)   -> similarExprs [x1, x2] [y1, y2]
            (Negate x1, Negate y1)   -> similarExpr x1 y1
            (Sqrt x1, Sqrt y1)       -> similarExpr x1 y1
            (Sym s1 xs1, Sym s2 ys1) -> s1 == s2 && similarExprs xs1 ys1
            _ -> x == y
 where
   xs = fromMaybe [x] $ match sumView x
   ys = fromMaybe [y] $ match sumView y
   
   setx = fromMaybe [x] $ match unionAssoView x
   sety = fromMaybe [y] $ match unionAssoView y

similarExprs :: [Expr] -> [Expr] -> Bool
similarExprs xs ys = 
   length xs == length ys && and (zipWith similarExpr xs ys)

unionAssoView :: View Expr [Expr]
unionAssoView = makeView f g
 where
   f expr = case match unionView expr of
               Just (x, y) -> (++) <$> f x <*> f y
               Nothing     -> return [expr]
   g = foldr1 (curry (build unionView))

commMinMax :: Expr -> Expr
commMinMax expr = fromMaybe expr $
   do (x, y) <- match minView expr
      guard (x > y)
      return (build minView (y, x))
 `mplus`
   do (x, y) <- match maxView expr
      guard (x > y)
      return (build maxView (y, x))

removeSame :: Eq a => [a] -> [a] -> ([a], [a])
removeSame = removeSameBy (==)

removeSameBy :: (a -> b -> Bool) -> [a] -> [b] -> ([a], [b])
removeSameBy _ [] ys = ([], ys)
removeSameBy f (x:xs) ys =
   case break (f x) ys of
      (ys1, _:ys2) -> removeSameBy f xs (ys1 ++ ys2)
      (_, [])      -> mapFirst (x:) (removeSameBy f xs ys)

leqExpr :: Expr -> Expr -> Bool
leqExpr x y = 
   case (match naturalView x, match naturalView y) of
      (Just i, Just j) -> i <= j
      _ | xs /= xs2 -> leqExpr (build sumView xs2) (build sumView ys2)
       where (xs2, ys2) = removeSame (map commMinMax xs) (map commMinMax ys)
      _ -> x == y
 where
   xs = fromMaybe [x] $ match sumView x
   ys = fromMaybe [y] $ match sumView y
   
lessExpr :: Expr -> Expr -> Bool
lessExpr x y = 
   case (match naturalView x, match naturalView y) of
      (Just i, Just j) -> i < j
      _ | xs /= xs2 -> lessExpr (build sumView xs2) (build sumView ys2)
       where (xs2, ys2) = removeSame (map commMinMax xs) (map commMinMax ys)
      _ -> False
 where
   xs = fromMaybe [x] $ match sumView x
   ys = fromMaybe [y] $ match sumView y

checkUnionACI :: Expr -> Expr -> Bool
checkUnionACI x y = f x == f y
 where
   f :: Expr -> S.Set Expr
   f e@(Sym _ cs) | isUnion e = S.unions (map f cs)
   f expr = S.singleton expr