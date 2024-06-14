{-# OPTIONS -Wno-missing-signatures #-}
module Domain.Logic.Inductive.Symbols where

import Domain.Logic.Formula hiding (Var)
import Domain.Math.Expr
import Ideas.Common.Rewriting (Symbol, newSymbol)
import Ideas.Common.View

function1 :: String -> (Symbol, Expr -> Expr, Expr -> Bool, View Expr Expr, View Expr a -> View Expr a)
function1 n = (s, build vw, (`belongsTo` vw), vw, with)
 where
   s  = newSymbol n
   vw = with identity
   
   with :: View Expr a -> View Expr a
   with va = makeView f g
    where
      f (Sym s2 [x]) | s2 == s = match va x
      f _ = Nothing
   
      g a = Sym s [build va a]

function2 :: String -> (Symbol, Expr -> Expr -> Expr, Expr -> Bool, View Expr (Expr, Expr), View Expr a -> View Expr b -> View Expr (a, b))
function2 n = (s, curry (build vw), (`belongsTo` vw), vw, with)
 where
   s  = newSymbol n
   vw = with identity identity
   
   with :: View Expr a -> View Expr b -> View Expr (a, b)
   with va vb = makeView f g
    where
      f (Sym s2 [x, y]) | s2 == s = (,) <$> match va x <*> match vb y
      f _ = Nothing
   
      g (a, b) = Sym s [build va a, build vb b]

function3 :: String -> (Symbol, Expr -> Expr -> Expr -> Expr, Expr -> Bool, View Expr (Expr, Expr, Expr), View Expr a -> View Expr b -> View Expr c -> View Expr (a, b, c))
function3 n = (s, curry3 (build vw), (`belongsTo` vw), vw, with)
 where
   s  = newSymbol n
   vw = with identity identity identity
   
   curry3 f x y z = f (x, y, z)
   
   with :: View Expr a -> View Expr b -> View Expr c -> View Expr (a, b, c)
   with va vb vc = makeView f g
    where
      f (Sym s2 [x, y, z]) | s2 == s = (,,) <$> match va x <*> match vb y <*> match vc z
      f _ = Nothing
   
      g (a, b,c ) = Sym s [build va a, build vb b, build vc c]   

(<->>) :: Expr -> Expr -> Expr
p <->> q = Sym impliesSymbol [p, q]

(.|=.) :: Expr -> Expr -> Expr
p .|=. q = Sym (newSymbol "cons") [p, q]

set :: [Expr] -> Expr
set = Sym (newSymbol "set")

isSet :: Expr -> Maybe [Expr]
isSet (Sym s xs) | s == newSymbol "set" = Just xs
isSet _ =  Nothing

isTSet :: Expr -> Bool
isTSet (Sym s _) = s == newSymbol "set"
isTSet _ = False

minm, maxm ::  Expr -> Expr -> Expr
(minSym, minm, isMin, minView, minWith) = function2 "min"
(maxSym, maxm, isMax, maxView, maxWith) = function2 "max"
(unionSym, union,isUnion, unionView, unionWith) = function2 "union"
(delSym, del, isDel, delView, delWith) = function2 "del"

nneg, star, impl, subf, val1, val2, stari, len, haakjes, bin, prop :: Expr -> Expr
(nnegSym, nneg, isNneg, nnegView, nnegWith) = function1 "nneg"
(starSym, star, isStar, starView, starWith) = function1 "star"
(stariSym, stari, isStari, starViewi, stariWith) = function1 "stari"
(star5Sym, star5, isStar5, star5View, star5With) = function1 "star5"
(implSym, impl, isImpl, implView, implWith) = function1 "impl"
(subfSym, subf, isSubf, subfView, subfWith) = function1 "subf"
(val1Sym, val1, isVal1, val1View, val1With) = function1 "val1"
(val2Sym, val2, isVal2, val2View, val2With) = function1 "val2"
(valSym, val, isVal, valView, valWith) = function1 "val"
(nnfSym ,nnf, isNnf, nnfView, nnfWith) = function1 "nnf"
(valASym, valA, isValA, valAView, valAWith) = function1 "valA"
(valBSym, valB, isValB, valBView, valBWith) = function1 "valB"
(binSym, bin, isBin, binView, binWith) = function1 "bin"
(propSym, prop, isProp, propView, propWith) = function1 "prop"
(lenSym, len, isLen, lenView, lenWith) = function1 "len"
(haakjesSym, haakjes, isHaakjes, haakjesView, haakjesWith) = function1 "haakjes"
(lengteSym, lengte, isLengte, lengteView, lengteWith) = function1 "lengte"
(revSym, rev, isRev, revView, revWith) = function1 "rev"
(gSym, funG, isG, gView, gWith) = function1 "g"
(suppSym, supp, isSupp, suppView, suppWith) = function1 "supp"

subst :: Expr -> Expr -> Expr -> Expr
(substSym, subst, isSubst, substView, substWith) = function3 "subst"

isImplies :: Expr -> Maybe (Expr, Expr)
isImplies (Sym s [p, q]) | s == impliesSymbol = Just (p, q)
isImplies _ = Nothing