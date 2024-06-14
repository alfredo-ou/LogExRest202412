module Domain.Logic.Inductive.ExprRules 
   ( exprRules, setRule, valAB, calculate, calculate2
   ) where

import Data.Maybe
import Domain.Logic.Inductive.Symbols
import Domain.Logic.Formula (SLogic)
import Domain.Logic.Rules
import Domain.Math.Expr hiding ((.*.))
import qualified Data.Set as S
import Ideas.Common.Library
import Domain.Logic.Inductive.ExprUtils 

exprRules :: [Rule Expr]
exprRules = [calculate, setRule, logicRule]


logicRule :: Rule Expr
logicRule = makeRule "logic" f
 where
   f = applyAll (choice (map fromLogicRule rs))

   rs :: [Rule SLogic]
   rs = [ruleDeMorganOr, ruleDeMorganAnd, ruleDoubleNeg, ruleTrueAnd]

   fromLogicRule :: Rule SLogic -> Rule Expr
   fromLogicRule = liftView (makeView fromExpr toExpr)

------------------------------------------------------------------------------
-- Rules



calculate :: Rule Expr
calculate = makeRule "calculate" f where
   -- plus-zero
   f (Nat 0 :+: x) = Just x
   f (x :+: Nat 0) = Just x
   -- plus-nat
   f (Nat x :+: Nat y) = Just (toExpr (x + y))
   -- distr
   f (Nat n :*: ( x :+: y )) =  rec (Nat n :*: ( x :+: y )) 

   --  Just (toExpr n:*:x :+: (toExpr n:*:y)) --     
   -- sub-nat
   f (Nat x :-: Nat y) = Just (toExpr (x - y))
   -- times-nat
   f (Nat x :*: Nat y) = Just (toExpr (x * y))
   -- min-nat
   f e@(Sym _ [Nat i, Nat j]) | isMin e = Just (Nat (i `min` j))
   -- min-distr
   f (Nat n :-: ( x :-: y )) = Just $ toExpr (Nat n :-: x) :+: toExpr y
   -- max-nat
   f e@(Sym _ [Nat i, Nat j]) | isMax e = Just (Nat (i `max` j))
   f _ = Nothing
   rec (Nat n :*: ( x :+: y )) =  Just  (toExpr ( rec(Nat n:*:x))  :+:( toExpr n:*:y)) 
   rec (Nat n :*: x  ) =   Just (toExpr n:*:x)
   rec _ =  Nothing 
   
calculate2 :: Rule Expr
calculate2 = makeRule "calculate" f where
   f (Nat n :*: x) = rec1 (Nat n :*: x)
   f _ = Nothing
   rec1 (Nat 1 :*: x) = Just (toExpr x)
   rec1 (Nat n :*: x) = Just (toExpr (rec1 (Nat(n - 1) :*: x)) :+: toExpr x)
   rec1 _ = Nothing

setOfStringsView :: View Expr (S.Set String)
setOfStringsView = makeView f g
 where
   f :: Expr -> Maybe (S.Set String)
   f e@(Sym _ [Var n ,l@(Sym _ [s])]) | isDel e && isTSet l && n `elem` ["p", "q", "r"] = Just $  S.delete n (fromJust $ f (set [s]))
   f e@(Sym _ [Var _ , Sym _ [_]]) | isDel e = Nothing
   f e@(Sym _ cs)
      | isUnion e = fmap S.unions (mapM f cs)
      | otherwise = 
           case isSet e of 
               Just xs -> fmap S.fromList (mapM fromVar xs)
               Nothing -> Nothing 
   f _ = Nothing
   
   fromVar (Var s) = Just s
   fromVar _ = Nothing
   
   g :: S.Set String -> Expr
   g = set . map Var . S.toList 
   
setRule :: Rule Expr
setRule = makeRule "set" $ \expr ->
   let new = simplify setOfStringsView expr
   in if not (expr `similarExpr` new) then return new else 
      applyAll (unionUnion .|. distrDel) expr
   
unionUnion :: Rule Expr  
unionUnion = makeRule "unionUnion" f 
 where
   varQ = set [Var "q"]

   f (Sym s1 [Sym s2 [x, y], q]) | s1 == unionSym && s2 == unionSym && q == varQ && isNotUnionQ x =
      Just $ union (x `union` varQ) (y `union` varQ)
   f _ = Nothing

   isNotUnionQ (Sym s [_, y]) | s == unionSym && y == varQ = False
   isNotUnionQ _ = True


distrDel :: Rule Expr  
distrDel = rewriteRule "distrDel" $ \n x y -> 
   del (Var n) (x `union` y) :~> del (Var n) x `union` del (Var n) y
    
-- this rules has a condition in the strategy
valAB :: Rule Expr
valAB = makeRule "valAB" f 
 where
   f :: Expr -> Maybe Expr
   f  e@(Sym _ [Var x])|  isValB e && x `elem` ["p", "q", "r"] =
      Just $ valA (Var x)
   f _ = Nothing