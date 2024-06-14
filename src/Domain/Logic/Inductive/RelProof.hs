module Domain.Logic.Inductive.RelProof
   ( readyRelProof
   , extendUpper', extendLower', somewhereExpr
   , closeEqual, closeLess, closeSame
   , applyIH
   , eqRelProof, checkRelProof, checkRelProof', similarRelProof,  checkIHRelProof'
   , getMetaVars
   , closeEqualProof, closeSameProof, closeLessProof
   , exprCloseRules, definitionCloseRules
   , stepAndClose
   , onCurrent, onCurrentBy
   ) where

import Control.Monad
import Data.Maybe
import Ideas.Common.Rewriting
import Domain.Logic.Formula ()
import Domain.Logic.Inductive.Theorem
import Domain.Logic.Inductive.Symbols
import Domain.Logic.Inductive.ExprRules
import Domain.Logic.Inductive.ExprUtils 
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.Definitions
import Domain.Logic.Inductive.RP
import Domain.Math.Expr hiding ((.*.))
import Ideas.Common.Constraint
import Ideas.Common.Derivation
import Ideas.Utils.Uniplate
import Ideas.Utils.Prelude
import Ideas.Common.Library hiding (many)
import Domain.Logic.Inductive.Relation
import qualified Data.Set as S

-------------------------------------------------------------------------

closeEqual :: Bool -> RelProof -> Maybe RelProof
closeEqual keepUpper rp = do
   (_, t, _) <- isOpen rp
   guard $ t `elem` [LessThanOrEqual, GreaterThanOrEqual, Equal, Equivalence]
   closeEq keepUpper similarExpr rp

closeSame :: RelProof -> Maybe RelProof
closeSame rp = do
   (l, t, r) <- isOpen rp
   guard $ similarExpr l r && l /= r && t `elem` [LessThanOrEqual, GreaterThanOrEqual, Equal, Equivalence]
   close "calculate.close" rp

closeLess ::  RelProof -> Maybe RelProof --hier nog een closeGreater maken!
closeLess rp = do
   (l, t, r) <- isOpen rp
   guard $ lessExpr l r && l /= r && t `elem` [LessThanOrEqual, LessThan]
   close "calculate.close" rp

readyRelProof :: Theorem -> RelProof -> Bool
readyRelProof th rp = isNothing (isOpen rp) && checkRelProof th rp

data Monotonicity = Increasing | Decreasing | NoMonotonicity
   deriving (Show, Eq)

monotonicity :: Expr -> [Monotonicity]
monotonicity (_ :+: _) = [Increasing, Increasing]
monotonicity expr 
   | isMax expr = [Increasing, Increasing]
   | isMin expr = [Increasing, Increasing]
   | otherwise  = repeat NoMonotonicity

monotonicityRelType :: RelType -> Monotonicity -> Bool
monotonicityRelType Equal           = const True
monotonicityRelType LessThan        = (== Increasing)
monotonicityRelType LessThanOrEqual = (== Increasing)
monotonicityRelType GreaterThan        = (== Decreasing)
monotonicityRelType GreaterThanOrEqual = (== Decreasing)
monotonicityRelType Equivalence     = const True

extendUpper' :: RelType -> Motivation -> (Expr -> [Expr]) -> RelProof -> [RelProof]
extendUpper' tp mot f p =
   case isOpen p of
      Just (a, _, _) -> catMaybes
         [ extendUpper (tp, mot) b p
         | b <- somewhereExpr tp f a
         ]
      Nothing -> []

extendLower' :: RelType -> Motivation -> (Expr -> [Expr]) -> RelProof -> [RelProof]
extendLower' tp mot f p =
   case isOpen p of
      Just (_, _, a) -> catMaybes
         [ extendLower (tp, mot) b p
         | b <- somewhereExpr tp f a
         ]
      Nothing -> []

somewhereExpr :: RelType -> (Expr -> [Expr]) -> Expr -> [Expr]
somewhereExpr tp = descendWith (monotonicityRelType tp)

descendWith :: (Monotonicity -> Bool) -> (Expr -> [Expr]) -> Expr -> [Expr]
descendWith mono f = rec 
 where
   rec expr = f expr ++
      [ mk y
      | (m, (x, mk)) <- zip (monotonicity expr) (holes expr)
      , mono m
      , y <- rec x
      ]

-----------------
-- Equivalence and similarity

-- equivalence

eqRelProof :: Theorem -> RelProof -> RelProof -> Bool
eqRelProof th rp1 rp2 =
   ( topExpr rp1 == topExpr rp2 &&
     bottomExpr rp1 == bottomExpr rp2 && 
     checkRelProof th rp1 && checkRelProof th rp2
   ) || (rp1 == rp2)

checkRelProof :: Theorem -> RelProof -> Bool
checkRelProof th = isNothing . isViolated (checkRelProof' th "") -- use "" for Maybe ProofStep: location is not relevant here

checkRelProof' :: Theorem -> String -> Constraint RelProof
checkRelProof' th loc = makeConstraint "check-relproof" $ \rp -> do
   let trs = triplesInProofDirection rp
   unless (null trs) $
      getResult (checkDerivation th loc) (isJust (isClosed rp), trs)
   unless (isJust (isClosed rp) || isJust (matchTheorem th (topExpr rp) (bottomExpr rp))) -- kan eruit???Nee!! want controleert of onder en boven dezelfde substitutie gebruiken, verhuizen???
      (violation $ loc ++ ":subproof is not an instance of theorem")
   case isOpen rp of
      Just (_, rt, _) | rt /= relationTypeForTheorem th ->
         violation $ loc ++ ":type does not match theorem"
      _ -> return ()
   unless (checkType rp)
      (violation $ loc ++ ":type does not match theorem")
 where
    checkType rp = maybe False (relationTypeForTheorem th `compareRelType`) (combineRelTypes (allRelTypes rp))
    
checkIHRelProof' :: Theorem -> String -> Constraint RelProof
checkIHRelProof'  th _ = makeConstraint "check-relproof" $ \rp ->
   case isClosed rp of  
      Just d -> 
  --       getResult (checkDerivation th location 0) (True, d)
             when (derivationLength d == 1 && ihMot)   $        --nakijken unless veranderd in when, nu hier de motivatie is ih toevoegen!
                     case matchLhs th (topExpr rp) of
                      Just _  -> return ()
                      Nothing ->  violation "wrongIHTop" 
               where ihMot = snd (head (steps d)) == "ih"       
      _ -> return ()
 --where
  --  checkType rp = maybe False (relationTypeForTheorem th `compareRelType`) (combineRelTypes (allRelTypes rp))
    
    
isRenaming :: Substitution -> Bool
isRenaming = all (f . snd)
 where
   f (TVar s) = s `elem` knownMetaVars
   f _ = False

-- There should be exactly one meta-var for a hypothesis
checkHypothesisVars :: Expr -> Expr -> Result ()
checkHypothesisVars e1 e2
   | s1 /= s2       = violation "different meta vars in hypothesis"  
   | S.size s1 == 0 = violation "no meta var in hypothesis"
   | S.size s1 > 1  = violation "multiple meta vars in hypothesis"  --komt niet voor???
   | otherwise      = return ()
 where
   s1 = getMetaVars e1
   s2 = getMetaVars e2

getMetaVars :: Expr -> S.Set String
getMetaVars = S.filter (`elem` knownMetaVars) . varSet

checkDerivation :: Theorem -> String -> Constraint (Bool, [(Bool, (Expr, Step, Expr))])
checkDerivation th loc = subConstraints f "check-subproof" (checkTriple th)
 where
   f (isCl, trs) = [ (loc ++ " linenr:"++  show i, (isCl && length trs == 1, t)) | (i, t) <- zip [0 :: Int ..] trs ]

-- For IH, the triple is either a definition step or an application step
checkTriple :: Theorem -> Constraint (Bool, (Bool, (Expr, Step, Expr)))
checkTriple th = makeConstraint "check-triple" $ \(definitionStep, (isTD, t@(expr1, (rt, mot), expr2))) -> 
   let resultMotivation = getResult (checkMotivation th) t in 
   let swapt = (expr2, (swapRelType rt, mot), expr1) in
   case findExprRule mot of 
      Just r
         | mot == "calculate" && any (checkCalculate rt expr1) (equivExpr expr2)
          ->    return ()
         | mot == "calculate" && any (checkCalculate (swapRelType rt) expr2) (equivExpr expr1)
          ->    return ()
         -- for calculate, just do the calculation and check, vervangen door regels hierboven die links of rechts vereenvoudigen
     --    | mot == "calculate" && checkCalculate rt expr1 expr2 ->
     --        return ()
         -- prevents recognizing forward/backward application with rt is < or >
         | mot == "calculate" && checkCalculate Equal expr1 expr2 -> 
             violation "miscalculation or wrong relation"
         | mot == "set" && rt == Equal && checkUnionACI expr1 expr2 -> 
             return ()
         -- check forward application
         | any (similarExpr expr2) (searchWithType rt r expr1) -> 
              return ()
         -- check backward application
         | any (similarExpr expr1) (searchWithType rt r expr2) -> 
              return ()
         -- recognized rule, but wrong relation  
         | any (similarExpr expr2) (searchWithoutType r expr1) -> 
              violation "wrong relation"   
         | any (similarExpr expr1) (searchWithoutType  r expr2) -> 
              violation "wrong relation"
 
         -- check backward application
        
         | similarExpr expr1 expr2 -> violation "similar-expr"
         | isTD && isError (getResult (checkApplicableRule r) t) -> getResult (checkApplicableRule r) t
         | not isTD && isError (getResult (checkApplicableRule r) swapt) -> getResult (checkApplicableRule r) swapt

      -- cases where there may not be a rule found
      _  | similarExpr expr1 expr2 -> violation "similar-expr"
         | mot == "ih" -> getResult (checkIH definitionStep isTD th) t        
         | isError resultMotivation ->
              resultMotivation
           -- failing cases (including cases with special feedback reporting)
         | mot == "calculate" -> violation "miscalculation"
      _ -> violation "step"
 where
   checkCalculate LessThan x y = lessExpr x y 
   checkCalculate LessThanOrEqual x y = leqExpr x y 
   checkCalculate Equal x y = similarExpr x y 
   checkCalculate GreaterThan x y = lessExpr y x
   checkCalculate GreaterThanOrEqual x y = leqExpr y x
   checkCalculate _ _ _  =  False

   isError (Violation _) = True
   isError _             = False

   searchWithType rt r expr = concat 
      [ somewhereExpr t1 (applyAll r) expr  -- er stond rt maar dan gebeurt er eigenlijk niets
      | (t1, t2) <- weakenRelTypeRule r
      , rt == t2
      ] 

   searchWithoutType  r expr = concat 
      [ (somewhereExpr rt (applyAll r) expr) | rt <- (map fst relationSymbols) ] 
         
   search rt r expr = concat 
      [ somewhereExpr rt (applyAll r) expr ] 

   equivExpr expr = expr : search Equal calculate expr ++ search Equal calculate2 expr

weakenRelTypeRule :: Rule Expr -> [(RelType, RelType)]  
weakenRelTypeRule r 
   | r == valAB = [(LessThanOrEqual,LessThanOrEqual)]
   | r `elem` definitionRules = 
   [ (Equal, LessThanOrEqual), (Equal, GreaterThanOrEqual) 
   , (Equal, Equal)
   ] 
   | r `elem` exprRules = [(Equal,Equal)]
   | otherwise  = [ (t, t) | t <- [GreaterThan .. Equivalence] ]
   
checkMotivation :: Theorem -> Constraint  (Expr, Step, Expr)
checkMotivation th = makeConstraint "check-motivation" $ \(expr1, (rt, mot), expr2) -> do
   let forw  = [ r | r <- inductiveRules
                   , e <- searchWithType rt r expr1
                   , similarExpr e expr2
               ]
       backw = [ r | r <- inductiveRules
                   , e <- searchWithType rt r expr2
                   , similarExpr e expr1
               ]
       ihstep = any (similarExpr expr2) (somewhereExprMany1 (relationTypeForTheorem th) (ihTransExpr th) expr1) 
       mots = map showId (forw ++ backw) ++ [ "ih" | ihstep ] 
   when (null mots) Irrelevant
   when (mot == "")         $ violation $ "missing motivation: " ++ head mots
   unless (mot `elem` mots) $ violation $ "wrong motivation: " ++ head mots
   where
      searchWithType rt r expr = concat 
       [ somewhereExpr t1 (applyAll r) expr  -- er stond rt maar dan gebeurt er eigenlijk niets
       | (t1, t2) <- weakenRelTypeRule r
       , rt == t2
       ]

-- constraints checks whether the rule mot is applicable, since calculate is always applicable, this rule is not included,
-- applicability check for ih in checkIH,  let op volgorde, eerst relatietype fout, daarna pas applicable rule

checkApplicableRule:: Rule Expr -> Constraint (Expr, Step, Expr)   
checkApplicableRule r = makeConstraint "check-applicablerule" $ \(expr1, (rt, mot), expr2) -> do    
      let forw = searchWithType  rt r expr1 --  somewhereExpr rt (applyAll r) expr1
      unless (null forw || head forw == expr2) $ violation $ show  mot ++ "is applicable, however the result is:  " ++ show (head forw)
      where 
         searchWithType rt r expr = concat 
          [ somewhereExpr t1 (applyAll r) expr  
           | (t1, t2) <- weakenRelTypeRule r
           , rt == t2
          ] 

-- For IH, the triple is either a definition step or an application step
checkIH :: Bool -> Bool -> Theorem -> Constraint (Expr, Step, Expr)
checkIH definitionStep isTD th = makeConstraint "check-ih" $ \(expr1, (rt, mot), expr2) -> do
   unless (mot == "ih") Irrelevant
   let ihstep {- |  mot == "ih" -} = somewhereExprMany1 (relationTypeForTheorem th) (ihTransExpr th) expr1
   unless (relationTypeForTheorem th == rt) (violation "relation type")
   unless (any (similarExpr expr2) (somewhereExprMany1 (relationTypeForTheorem th) (ihTransExpr th) expr1)) $  
      case checkHypothesisVars expr1 expr2 of
         _ | isTD && not definitionStep && not (null ihstep) -> violation $ "the induction hypothesis is applicable, however the result is: " ++ show (head ihstep) 
         _ | not definitionStep  ->  violation "incorrect application ih"
         res@(Violation _) -> res
         _ -> violation "incorrect definition ih"

-- this traversal combinator is used for checking application of induction hypothesis; it 
-- allows one or more applications at once
somewhereExprMany1 :: RelType -> (Expr -> [Expr]) -> Expr -> [Expr]
somewhereExprMany1 t f = concatMap rec . somewhereExpr t f
 where
   rec e = e : somewhereExprMany1 t f e

applyIH :: RelProof -> Theorem -> Maybe RelProof
applyIH rp th =
   let t = ihTransProof "ih" th
   in listToMaybe (map fst (transApply t rp))

-- transform under associativity of union (with a left and right context)
ihTransExpr :: Theorem -> Expr -> [Expr]
ihTransExpr th e0 = 
   [ build unionAssoView (lefts ++ new : rights)
   | (lefts, middle, rights) <- split3 (fromMaybe [e0] $ match unionAssoView e0)
   , not (null middle)
   , new <- f (build unionAssoView middle)
   ] 
 where 
   f e = do
      (sub, rhs) <- maybeToList $ matchLhs th e
      guard (isRenaming sub)
      return rhs

relTypeForIH :: Theorem -> RelType -> Maybe RelType
relTypeForIH th rt =  
   case relationTypeForTheorem th of 
      LessThan -> do
         guard (rt `elem` [LessThanOrEqual, LessThan])
         return LessThanOrEqual
      GreaterThan -> do
         guard (rt `elem` [GreaterThanOrEqual, GreaterThan])
         return GreaterThanOrEqual
      tp -> return tp
            
ihTransProof :: IsId n => n -> Theorem -> Transformation RelProof
ihTransProof n th = makeTrans f
 where
   f :: RelProof -> [RelProof]
   f rp = do
      (_, rt, _) <- maybeToList (isOpen rp)
      tp  <- maybeToList (relTypeForIH th rt)
      new <- extendUpper' (relationTypeForTheorem th) (showId $ newId n) (ihTransExpr th) rp
      return (replaceType tp new)

findExprRule :: Motivation -> Maybe (Rule Expr)
findExprRule mot = 
   case filter isMot inductiveRules of
      [r] -> Just r
      _   -> Nothing
 where
   isMot r = showId r == mot

inductiveRules :: [Rule Expr]
inductiveRules = definitionRules ++ valAB : exprRules

-- similarity
similarRelProof :: RelProof -> RelProof -> Bool
similarRelProof = eqRelProofBy similarExpr

exprCloseRules :: [Rule RelProof]
exprCloseRules = map (stepAndClose . onCurrent) exprRules

definitionCloseRules :: [Rule RelProof]
definitionCloseRules = map (stepAndClose . onCurrent) definitionRules

stepAndClose :: Rule RelProof -> Rule RelProof
stepAndClose r = makeRule (getId r # "close") (applyAll (r .*. closeEqualProof))

closeEqualProof :: Rule RelProof
closeEqualProof = makeRule "close.equal" (closeEqual True)

closeSameProof :: Rule RelProof
closeSameProof = makeRule "close.same" closeSame

closeLessProof :: Rule RelProof
closeLessProof = makeRule "close.less" closeLess

onCurrent :: Rule Expr -> Rule RelProof
onCurrent = onCurrentBy Equal

onCurrentBy :: RelType -> Rule Expr -> Rule RelProof
onCurrentBy rt r  = makeRule (getId r) f 
 where
   f rp = extendUpper' rt (showId r) (applyAll r) rp ++
          extendLower' rt (showId r) (applyAll r) rp