-- to do: remove lists of base case variables (break cyclic dependency)
-- to do: use of phi/psi is confusion: use other names instead
module Domain.Logic.Inductive.Definitions (definitionRules) where

import Data.Maybe
import Domain.Logic.Inductive.Symbols
import Domain.Math.Expr hiding ((.*.))
import Domain.Algebra.Boolean
import Ideas.Common.Library

definitionRules :: [Rule Expr]
definitionRules = 
   [ starDef, nnegDef, implDef, subfDef, val1Def, lenDef, haakjesDef, propDef
   , binDef, valADef, valBDef, star5Def, nnfDef, lengteDef, stariDef
   , valDef, revDef, gDef, substDef, suppDef,val2Def
   ]

ruleRewrites :: IsId n => n -> [RewriteRule a] -> Rule a
ruleRewrites n = ruleTrans n . mconcat . map transRewrite

----------------

starDef :: Rule Expr
starDef = makeRule "star" f where
  f e@(Sym _ [Var n]) | isStar e && n `elem` ["p", "q", "r"] =  Just (Var n)
  f e@(Sym _ [l@(Sym _ [phi])]) | isStar e && isJust (isComplement l) = Just $ complement (star phi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStar e && isJust (isAnd l) = Just $ star phi <&&> star psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStar e && isJust (isOr l)  = Just $ star phi <||> star psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStar e && isJust (isImplies l) = Just $ complement (star phi) <||> star psi
  f _ = Nothing
  
stariDef :: Rule Expr
stariDef = makeRule "stari" f where
  f e@(Sym _ [Var n]) | isStari e && n == "p" =  Just (Var n)
  f e@(Sym _ [Var n]) | isStari e && n `elem` ["q", "r"] =  Just (Var n<->> Var  "p" )
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStari e && isJust (isImplies l) = Just $ stari phi <->> stari psi
  f _ = Nothing  
  
star5Def :: Rule Expr
star5Def = makeRule "star5" f where
  f e@(Sym _ [Var n]) | isStar5 e && n `elem` ["p", "q", "r"] = Just $  complement(Var n)
  f e@(Sym _ [l@(Sym _ [phi])]) | isStar5 e && isJust (isComplement l) = Just $ complement (star5 phi)
 -- f e@(Sym _ [l@(Sym _ [Var n])]) | isStar5 e && isJust (isComplement l)&& n `elem` ["p", "q", "r"] = Just (Var n)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStar5 e && isJust (isAnd l) = Just $ star5 phi <||> star5 psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isStar5 e && isJust (isOr l)  = Just $ star5 phi <&&> star5 psi
  f _ = Nothing  
  
nnfDef :: Rule Expr
nnfDef = makeRule "nnf" f where
  f e@(Sym _ [Var n]) | isNnf e && n `elem` ["p", "q", "r"] = Just true
  f e@(Sym _ [l@(Sym _ [Var n])]) | isNnf e && isJust (isComplement l)&& n `elem` ["p", "q", "r"] = Just true
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isNnf e && isJust (isAnd l) = Just $ nnf phi <&&> nnf psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isNnf e && isJust (isOr l)  = Just $ nnf phi <&&> nnf psi
  f _ = Nothing 
  
nnegDef :: Rule Expr
nnegDef = makeRule "nneg" f where
  f e@(Sym _ [Var n]) | isNneg e && n `elem` ["p", "q", "r"] = Just 0
  f e@(Sym _ [l@(Sym _ [phi])]) | isNneg e && isJust (isComplement l) = Just $ 1 + nneg phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isNneg e && isJust (isAnd l) = Just $ nneg phi + nneg psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isNneg e && isJust (isOr l)  = Just $ nneg phi + nneg psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isNneg e && isJust (isImplies l) = Just $ nneg phi + nneg psi
  f _ = Nothing
  
implDef :: Rule Expr
implDef = makeRule "impl" f where
  f e@(Sym _ [Var n]) | isImpl e && n `elem` ["p", "q", "r"] = Just 0
  f e@(Sym _ [l@(Sym _ [phi])]) | isImpl e && isJust (isComplement l) = Just $ impl phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isImpl e && isJust (isAnd l) = Just $ impl phi + impl psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isImpl e && isJust (isOr l)  = Just $ impl phi + impl psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isImpl e && isJust (isImplies l) = Just $ 1 + impl phi + impl psi
  f _ = Nothing
  
subfDef :: Rule Expr
subfDef = makeRule "subf" f where
  f e@(Sym _ [Var n]) | isSubf e && n `elem` ["p", "q", "r"] = Just 1
  f e@(Sym _ [l@(Sym _ [phi])]) | isSubf e && isJust (isComplement l) = Just $ 1 + subf phi 
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isSubf e && isJust (isAnd l) = Just $ 1 + subf phi + subf psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isSubf e && isJust (isOr l)  = Just $ 1 + subf phi + subf psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isSubf e && isJust (isImplies l) = Just $ 1 + subf phi + subf psi
  f _ = Nothing  

revDef :: Rule Expr
revDef = makeRule "rev" f where
  f e@(Sym _ [Var n]) | isRev e && n `elem` ["p", "q", "r"] = Just $ Var n
  f e@(Sym _ [l@(Sym _ [phi])]) | isRev e && isJust (isComplement l) = Just $ complement (rev phi) 
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isRev e && isJust (isAnd l) = Just $  rev psi <&&> rev phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isRev e && isJust (isOr l)  = Just $  rev psi <||> rev phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isRev e && isJust (isImplies l) = Just $ complement (rev psi) <->> complement (rev phi)
  f _ = Nothing  
  
valDef :: Rule Expr
valDef = makeRule "val" f where
  f e@(Sym _ [l@(Sym _ [phi])]) | isVal e && isJust (isComplement l) = Just $ 1 - val phi 
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal e && isJust (isAnd l) = Just $ minm (val phi) (val psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal e && isJust (isOr l)  = Just $ maxm (val phi) (val psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal e && isJust (isImplies l) = Just $ maxm( 1 - val phi)( val psi)
  f _ = Nothing    
  
val1Def :: Rule Expr
val1Def = makeRule "val1" f where
  f e@(Sym _ [Var n]) | isVal1 e && n `elem` ["p", "q", "r"] = Just 1
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal1 e && isJust (isAnd l) = Just $ minm (val1 phi) (val1 psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal1 e && isJust (isOr l)  = Just $ maxm (val1 phi) (val1 psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal1 e && isJust (isImplies l) = Just $ maxm( 1 - val1 phi)( val1 psi)
  f _ = Nothing  
  
val2Def :: Rule Expr
val2Def = makeRule "val2" f where
  f e@(Sym _ [Var n]) | isVal2 e && n == "p" = Just 1
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal2 e && isJust (isAnd l) = Just $ minm (val2 phi) (val2 psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal2 e && isJust (isOr l)  = Just $ maxm (val2 phi) (val2 psi) 
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isVal2 e && isJust (isImplies l) = if val2 psi == val2  (Var "p") then Just  (val2  (Var "p")) else   Just $ maxm( 1 - val2 phi)( val2 psi)
  f _ = Nothing    
  
valADef :: Rule Expr
valADef = makeRule "valA" f where
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isValA e && isJust (isAnd l) = Just $ minm (valA phi) (valA psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isValA e && isJust (isOr l)  = Just $ maxm (valA phi) (valA psi)
  f _ = Nothing  
  
valBDef :: Rule Expr
valBDef = makeRule "valB" f where
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isValB e && isJust (isAnd l) = Just $ minm (valB phi) (valB psi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isValB e && isJust (isOr l)  = Just $ maxm (valB phi) (valB psi)
  f _ = Nothing   
 
lenDef :: Rule Expr
lenDef = makeRule "len" f where
  f e@(Sym _ [Var n]) | isLen e && n `elem` ["p", "q", "r"] = Just 1
  f e@(Sym _ [l@(Sym _ [phi])]) | isLen e && isJust (isComplement l) = Just $ 1 + len phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLen e && isJust (isAnd l) = Just $ 3 +  len phi +  len psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLen e && isJust (isOr l)  = Just $ 3 +  len phi +  len psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLen e && isJust (isImplies l) = Just $ 3 +  len phi +  len psi
  f _ = Nothing    
  
lengteDef :: Rule Expr
lengteDef = makeRule "lengte" f where
  f e@(Sym _ [Var n]) | isLengte e && n `elem` ["p", "q", "r"] = Just 1
  f e@(Sym _ [l@(Sym _ [phi])]) | isLengte e && isJust (isComplement l) = Just $ 1 + lengte phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLengte e && isJust (isAnd l) = Just $ 1 +  lengte phi +  lengte psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLengte e && isJust (isOr l)  = Just $ 1 +  lengte phi +  lengte psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isLengte e && isJust (isImplies l) = Just $ 1 +  lengte phi +  lengte psi
  f _ = Nothing    

haakjesDef :: Rule Expr
haakjesDef = makeRule "haakjes" f where
  f e@(Sym _ [Var n]) | isHaakjes e && n `elem` ["p", "q", "r"] = Just 0
  f e@(Sym _ [l@(Sym _ [phi])]) | isHaakjes e && isJust (isComplement l) = Just $  haakjes phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isHaakjes e && isJust (isAnd l) = Just $ 2 +  haakjes phi + haakjes psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isHaakjes e && isJust (isOr l)  = Just $ 2 +  haakjes phi + haakjes psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isHaakjes e && isJust (isImplies l) = Just $ 2 +  haakjes phi + haakjes psi
  f _ = Nothing   
  
propDef :: Rule Expr
propDef = makeRule "prop" f where
  f e@(Sym _ [Var n]) | isProp e && n `elem` ["p", "q", "r"] = Just 1
  f e@(Sym _ [l@(Sym _ [phi])]) | isProp e && isJust (isComplement l) = Just $  prop phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isProp e && isJust (isAnd l) = Just $  prop phi + prop psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isProp e && isJust (isOr l)  = Just $  prop phi + prop psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isProp e && isJust (isImplies l) = Just $  prop phi + prop psi
  f _ = Nothing  
  
  
binDef :: Rule Expr
binDef = makeRule "bin" f where
  f e@(Sym _ [Var n]) | isBin e && n `elem` ["p", "q", "r"] = Just 0
  f e@(Sym _ [l@(Sym _ [phi])]) | isBin e && isJust (isComplement l) = Just $  bin phi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isBin e && isJust (isAnd l) = Just $ 1 +  bin phi + bin psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isBin e && isJust (isOr l)  =  Just $ 1 +  bin phi + bin psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isBin e && isJust (isImplies l) =  Just $ 1 +  bin phi + bin psi
  f _ = Nothing    
  
  
gDef :: Rule Expr
gDef = makeRule "g" f where
  f e@(Sym _ [Var n]) | isG e && n `elem` ["p", "q", "r"] =  Just (Var n)
  f e@(Sym _ [l@(Sym _ [phi])]) | isG e && isJust (isComplement l) = Just $ complement (funG phi)
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isG e && isJust (isAnd l) = Just $ complement(complement (funG phi) <||> complement(funG psi))
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isG e && isJust (isOr l)  = Just $ funG phi <||> funG psi
  f e@(Sym _ [l@(Sym _ [phi, psi])]) | isG e && isJust (isImplies l) = Just $ complement (funG phi) <||> funG psi
  f _ = Nothing
  
substDef :: Rule Expr
substDef = ruleRewrites "subst" $
   [ makeRewriteRule "subst" $ \chi -> 
        if n == m
        then subst chi (Var n) (Var m) :~> chi
        else subst chi (Var n) (Var m) :~> Var m
   | n <- ["p", "q", "r"]
   , m <- ["p", "q", "r"]
   ] ++
   [ makeRewriteRule "subst" $ \chi n x -> 
        subst chi (Var n) (complement x) :~> complement (subst chi (Var n) x)
   , makeRewriteRule "subst" $ \chi n x y -> 
        subst chi (Var n) (x <&&> y) :~> subst chi (Var n) x <&&> subst chi (Var n) y
   , makeRewriteRule "subst" $ \chi n x y -> 
        subst chi (Var n) (x <||> y) :~> subst chi (Var n) x <||> subst chi (Var n) y
   , makeRewriteRule "subst" $ \chi n x y -> 
        subst chi (Var n) (x <->> y) :~> subst chi (Var n) x <->> subst chi (Var n) y
   ]
  
suppDef :: Rule Expr
suppDef = ruleRewrites "supp" $
   [ makeRewriteRule "supp" $ supp (Var v) :~> set [Var v]
   | v <- ["p", "q", "r"]
   ] ++
   [ makeRewriteRule "supp" $ \x -> supp (complement x) :~> supp x
   , makeRewriteRule "supp" $ \x y -> supp (x <&&> y) :~> union (supp x) (supp y)
   , makeRewriteRule "supp" $ \x y -> supp (x <||> y) :~> union (supp x) (supp y)
   , makeRewriteRule "supp" $ \x y -> supp (x <->> y) :~> union (supp x) (supp y)
   ]