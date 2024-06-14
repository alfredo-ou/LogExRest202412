{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-- Exercise for the logic domain: to prove two propositions equivalent
--
-----------------------------------------------------------------------------

module Domain.Logic.Equivalence.Exercise
   ( proofExercise, proofTopExercise, proofUnicodeExercise
   ) where

import Control.Monad
import Data.List
import Data.Maybe
import Domain.Logic.BuggyRules
import Domain.Logic.Examples
import Domain.Logic.NormalForms.Exercises (extraLogicRules)
import Domain.Logic.Formula
import Domain.Logic.Generator (equalLogicA, equalLogicAC)
import Domain.Logic.InverseRules hiding (inverseRules)
import Domain.Logic.Parser
import Domain.Logic.Rules
import Domain.Logic.Strategies
import Domain.Logic.Utils
import Domain.Math.Expr ()
import Ideas.Common.Library
import Ideas.Common.Strategy.Legacy
import Ideas.Common.Traversal.Navigator
import Ideas.Utils.Prelude (ShowString(..), isSubsetOf, split)
import Prelude hiding ((<*>))

_seeAll :: IO ()
_seeAll = mapM_ _see [0 .. 41]

_see :: Int -> IO ()
_see n = printDerivation proofExercise (examplesAsList proofExercise !! n)

-- Currently, we use the DWA strategy
proofExercise :: Exercise Proof
proofExercise = makeExercise
   { exerciseId     = describe "Prove two propositions equivalent" $
                         propositionalId # "proof"
   , status         = Experimental
   , parser         = mapSecond makeProof . parseLogicProof False
   , prettyPrinter  = showProof
   , equivalence    = withoutContext equivalentProofs
   , similarity     = withoutContext similarProofs
   , suitable       = predicate $ all (uncurry eqLogic) . subProofs
   , ready          = predicate $ all (uncurry equalLogicA) . subProofs
   , strategy       = proofStrategy
   , extraRules     = liftToContext generalAssocProof : liftToContext generalCommutativityProof : 
                      map use (filter ((/= assocId) . getId) extraLogicRules)
                      ++ inverseRules ++ map useC buggyRules
   , ruleOrdering   = ruleOrderingWith proofOrder
   , navigation     = termNavigator
   , examples       = fmap makeProof exampleProofs
   }

proofUnicodeExercise :: Exercise Proof
proofUnicodeExercise = proofExercise
   { exerciseId    = describe "Prove two propositions equivalent (unicode support)" $
                        propositionalId # "proof.unicode"
   , parser        = mapSecond makeProof . parseLogicProof True
   , prettyPrinter = showProofUnicode
   }

proofTopExercise :: Exercise Proof
proofTopExercise = proofExercise
   { exerciseId    = describe "Prove two propositions equivalent (with top-level decomposition)" $
                        propositionalId # "proof.top"
   , parser        = mapSecond makeProof . parseLogicProof False
   , prettyPrinter = showSubProofs
   , equivalence   = withoutContext eqSubProofs
   , similarity    = withoutContext simSubProofs
   }

type Proof = (SLogic, SLogic)

assocId :: Id
assocId = getId generalAssocProof

-- associativity, possibly multiple: only recognizer
generalAssocProof :: Rule Proof
generalAssocProof = addRecognizerBool similarProofs $ setMinor True $ siblingOf groupAssociativity $ makeSimpleRule "assoc" (const Nothing)

generalCommutativityProof :: Rule Proof
generalCommutativityProof = addRecognizerBool isCom $ siblingOf groupCommutativity $ makeSimpleRule "comm" (const Nothing)
 where
   isCom (p1, q1) (p2, q2) = 
      equalLogicAC p1 p2 && equalLogicAC q1 q2 &&
      ( (p1 == p2 && not (equalLogicA q1 q2)) || 
        (q1 == q2 && not (equalLogicA p1 p2)))

proofOrder :: [Id]
proofOrder = []

subProofs :: Proof -> [(SLogic, SLogic)]
subProofs = return

makeProof :: (SLogic, SLogic) -> Proof
makeProof = id -- pair =
   -- let p = Var pair in p 
   {-
   case apply (topIsOr <|> topIsAnd <|> topIsNot <|> topIsEquiv <|> topIsImpl) p of
      Just (Var eq1 :||:  Var eq2) -> makeProof eq1 :||:  makeProof eq2
      Just (Var eq1 :&&:  Var eq2) -> makeProof eq1 :&&:  makeProof eq2
      Just (Var eq1 :->:  Var eq2) -> makeProof eq1 :->:  makeProof eq2
      Just (Var eq1 :<->: Var eq2) -> makeProof eq1 :<->: makeProof eq2
      Just (Not (Var eq))          -> Not (makeProof eq)
      _ -> p -}

proofPair :: Proof -> (SLogic, SLogic)
proofPair = id -- x = (catLogic (fmap fst x), catLogic (fmap snd x))

-- returns the current formula (with the focus) and its mirror
currentPair :: Context Proof -> Maybe (SLogic, SLogic)
currentPair ctx = do
   p <- currentTerm ctx >>= fromTerm
   let mirLoc = mirrorLoc (location ctx)
   mirCtx <- navigateTo mirLoc ctx
   q <- currentTerm mirCtx >>= fromTerm
   return (p, q)

setCurrentPair :: (SLogic, SLogic) -> Context Proof -> Maybe (Context Proof)
setCurrentPair (lhs, rhs) ctx = 
   (setAt mirLoc rhs >=> setAt loc lhs) ctx
 where
   setAt l a = navigateTo l >=> changeTerm (\_ -> Just (toTerm a))
   loc    = location ctx
   mirLoc = mirrorLoc loc

mirrorLoc :: Location -> Location
mirrorLoc = toLocation . f . fromLocation
 where   
   f []     = []
   f (i:is) = (1-i):is

showProof :: Proof -> String
showProof = uncurry f . proofPair
 where
   f p q = prettyLogic p ++ " == " ++ prettyLogic q

showProofUnicode :: Proof -> String
showProofUnicode = uncurry f . proofPair
 where
   f p q = ppLogicUnicode p ++ " == " ++ ppLogicUnicode q

showSubProofs :: Proof -> String
showSubProofs = intercalate ", " . map (uncurry f) . subProofs
 where
   f p q = show p ++ " == " ++ show q

equivalentProofs :: Proof -> Proof -> Bool
equivalentProofs proof1 proof2 =
   let (p1, q1) = proofPair proof1
       (p2, q2) = proofPair proof2
   in eqLogic p1 p2 && eqLogic q1 q2

similarProofs :: Proof -> Proof -> Bool
similarProofs proof1 proof2 =
   let (p1, q1) = proofPair proof1
       (p2, q2) = proofPair proof2
   in equalLogicA p1 p2 && equalLogicA q1 q2

eqSubProofs :: Proof -> Proof -> Bool
eqSubProofs proof1 proof2 =
   let ok = uncurry eqLogic
   in all ok (subProofs proof1) == all ok (subProofs proof2)

simSubProofs :: Proof -> Proof -> Bool
simSubProofs proof1 proof2 =
   let (xs1, xs2) = unzip (subProofs proof1)
       (ys1, ys2) = unzip (subProofs proof2)
       ok = uncurry equalLogicA
   in length xs1 == length ys1
   && all ok (zip xs1 ys1)
   && all ok (zip xs2 ys2)

proofStrategy :: LabeledStrategy (Context Proof)
proofStrategy = label "proof equivalent" $
   repeatS (
      -- somewhere splitTop
      -- disabled: first investigate how the common subexpressions should be
      -- communicated to the client
      -- |> somewhere commonExprAtom
         splitTop failS
      |> splitTop (useC towardsDNF)
      |> splitTop (commonLiteralSpecial |> commonLiteral)
      |> somewhere (check (not . isSplit) <*> toStrategy (useC distrAnd))
      )
      <*> normStrategy

splitTop :: Strategy (Context Proof) -> Strategy (Context Proof)
splitTop s =  fix $ \a -> 
   check canSplit <*> layer [] a 
   <|> check (not . canSplit) <*> (((topIsOr |> topIsOrCom) <|> (topIsAnd |> topIsAndCom)) |> s)

isSplit :: Context Proof -> Bool 
isSplit ctx = canSplit ctx && maybe True isSplit (up ctx)
        
canSplit :: Context Proof -> Bool
canSplit ctx = 
   case currentPair ctx of
      Just (p1 :&&: p2,  q1 :&&: q2)  -> eqLogic p1 q1 && eqLogic p2 q2
      Just (p1 :||: p2,  q1 :||: q2)  -> eqLogic p1 q1 && eqLogic p2 q2
      Just (p1 :->: p2,  q1 :->: q2)  -> eqLogic p1 q1 && eqLogic p2 q2
      Just (p1 :<->: p2, q1 :<->: q2) -> eqLogic p1 q1 && eqLogic p2 q2
      Just (Not p, Not q) -> eqLogic p q
      _ -> null (fromLocation (location ctx))

{-
splitTop :: Strategy (Context Proof)
splitTop =  use topIsNot <|> use topIsEquiv <|> use topIsImpl
               -- only use commutativity if not already in desired order
           <|> (use topIsAnd |> use topIsAndCom)
           <|> (use topIsOr  |> use topIsOrCom) 
-}

commonLiteralSpecial :: Strategy (Context Proof)
commonLiteralSpecial =
   repeatS ruleCommonLiteralSpecialInFront
   <*>
   repeat1 (somewhere ruleInvDistrCommonLiteral)
--   <*>
--  repeatS (somewhere topIsAnd)

ruleCommonLiteralSpecialInFront :: Rule (Context Proof)
ruleCommonLiteralSpecialInFront = siblingOf groupCommutativity $ makeRule "command.common-literal-special" f
 where
   f ctx = 
      case currentPair ctx of
         Just eq -> catMaybes $
            [ setCurrentPair x ctx | x <- maybeToList (findInFrontLeft eq) ] ++
            [ setCurrentPair (swap x) ctx | x <- maybeToList (findInFrontLeft (swap eq)) ]
         Nothing -> []

   findInFrontLeft eq@(p1 :&&: p2, q)
      | isAtomic p1 && isDNF p2 && all (`notElem` varsLogic p2) (varsLogic p1) && isDNF q = do
           lit <- listToMaybe (findCommonLiteral (p1, q))
           res <- inFrontLeft lit (swap eq)
           return (swap res)
   findInFrontLeft _ = Nothing

checkDNF :: Rule (Context Proof)
checkDNF = minor $ makeRule "is-dnf" $ \ctx -> do
   (p, q) <- currentPair ctx
   guard (isDNF p && isDNF q)
   return ctx

{- ------------------------------------------------------------------
In the strong-normalization strategy we do not check for common literals:
   |> somewhere (use checkDNF <*> commonLiteral)
Therefore, we also do not need simplification rules:
   |> somewhere (use ruleFalseAnd <|> use ruleTrueOr
                <|> use ruleFalseOr <|> use ruleTrueAnd)
   |> somewhere (use ruleComplAnd)
------------------------------------------------------------------ -}

normStrategy :: Strategy (Context Proof)
normStrategy = repeatS $
   splitTop (somewhere (
         use ruleIdempOr   <|>
         use ruleIdempAnd  <|>
         use absorptionOrSubset <|>
         use ruleComplOr
      ))
   |> splitTop (somewhereOrG introduceVar)

-- (p /\ q) \/ ... \/ (p /\ q /\ r)    ~> (p /\ q) \/ ...
--    (subset relatie tussen rijtjes: bijzonder geval is gelijke rijtjes)
absorptionOrSubset :: Rule SLogic
absorptionOrSubset = siblingOf groupAbsorption $ ruleList "absorpor-subset" $ \p -> do
   let xss = map conjunctions (disjunctions p)
       yss = nub $ filter (\xs -> all (ok xs) xss) xss
       ok xs ys = not (ys `isSubsetOf` xs) || xs == ys
   guard (length yss < length xss)
   return $ ors (map ands yss)

-----------------------------------------------------------------------------

towardsDNF :: Strategy (Context Proof)
towardsDNF = configureS (Reinsert `byName` specialGroupLiterals) $
   useC orRules <|> 
   {- somewhereOr ?? -} useC nnfStep

-- disabled for now:
-- Find a common subexpression that can be treated as a box
{-
commonExprAtom :: Rule (Context Proof)
commonExprAtom = minor $ ruleTrans "commonExprAtom" $ makeTransLiftContext $ \proof ->
   case proof of
      Var (p, q) -> do
         sub <- substRef :? []
         let xs = filter (same <&&> complement isAtomic) (largestCommonSubExpr p q)
             same cse = eqLogic (substitute cse p) (substitute cse q)
             used = varsLogic p `union` varsLogic q `union` map (ShowString . fst) sub
             new  = head (logicVars \\ used)
             substitute a this
                | a == this = Var new
                | otherwise = descend (substitute a) this
         case xs of
            hd:_ -> do
               substRef := (show new, show hd):sub
               return (Var (substitute hd p, substitute hd q))
            _ -> fail "not applicable"
      _ -> fail "not applicable"

largestCommonSubExpr :: (Uniplate a, Ord a) => a -> a -> [a]
largestCommonSubExpr x = rec
 where
   uniX  = S.fromList (universe x)
   rec y | y `S.member` uniX = [y]
         | otherwise         = concatMap rec (children y)

substRef :: Ref [(String, String)]
substRef = makeRef "subst"

logicVars :: [ShowString]
logicVars = [ ShowString [c] | c <- ['a'..] ]
-}
--------------------------------------------------------------------

acTopRuleFor :: Bool -> (forall a . Isomorphism (Logic a) [Logic a])
             -> Proof -> [Proof]
acTopRuleFor com iso (lhs, rhs) = do
   let as = from iso lhs
       bs = from iso rhs
       splitter = if com then divide else split
   (as1, as2, bs1, bs2) <- splitTwoLists splitter as bs
   let eqList xs ys = eqLogic (to iso xs) (to iso ys)
   guard (eqList as1 bs1 && eqList as2 bs2)
   return $
      -- if both sides have changed ...
      if as1++as2 /= as && bs1++bs2 /= bs
      then -- ... only keep the reordering on the left-hand side
         (to iso (as1++as2), rhs)
      else -- ... otherwise, decompose proof with "top" rule
         ( to iso [to iso as1, to iso as2]
         , to iso [to iso bs1, to iso bs2]
         )

splitTwoLists :: (forall t . [t] -> [([t], [t])])
              -> [a] -> [b] -> [([a], [a], [b], [b])]
splitTwoLists f as bs =
   [ (as1, as2, bs1, bs2)
   | (as1, as2) <- f as
   , not (null as1 || null as2)
   , (bs1, bs2) <- f bs
   , not (null bs1 || null bs2)
   ]

divide :: [a] -> [([a], [a])] -- associative + commutative
divide = foldr op [([], [])]
 where
   op a xs = map addLeft xs ++ map addRight xs
    where
      addLeft  (ys, zs) = (a:ys, zs)
      addRight (ys, zs) = (ys, a:zs)

topIsAnd :: Rule (Context Proof)
topIsAnd = minor $ makeRule "top-is-and" $ \ctx -> do
   pair <- maybeToList (currentPair ctx)
   new  <- acTopRuleFor False (collect andView) pair
   maybeToList (setCurrentPair new ctx)

topIsOr :: Rule (Context Proof)
topIsOr = minor $ makeRule "top-is-or" $ \ctx -> do
   pair <- maybeToList (currentPair ctx)
   new <- acTopRuleFor False (collect orView) pair
   maybeToList (setCurrentPair new ctx)

topIsAndCom :: Rule (Context Proof)
topIsAndCom = siblingOf groupCommutativity $ makeRule "top-is-and.com" $ \ctx -> do
   pair <- maybeToList (currentPair ctx)
   new  <- acTopRuleFor True (collect andView) pair
   maybeToList (setCurrentPair new ctx)

topIsOrCom :: Rule (Context Proof)
topIsOrCom = siblingOf groupCommutativity $ makeRule "top-is-or.com" $ \ctx -> do
   pair <- maybeToList (currentPair ctx)
   new  <- acTopRuleFor True (collect orView) pair
   maybeToList (setCurrentPair new ctx)
{-
topIsEquiv :: Rule Proof
topIsEquiv = minorRule "top-is-equiv" f
 where
   f (Var (p :<->: q, r :<->: s)) = do
      guard (eqLogic p r && eqLogic q s)
      return (Var (p, r) :<->: Var (q, s))
   f _ = Nothing

topIsImpl :: Rule Proof
topIsImpl = minorRule "top-is-impl" f
 where
   f (Var (p :->: q, r :->: s)) = do
      guard (eqLogic p r && eqLogic q s)
      return (Var (p, r) :->: Var (q, s))
   f _ = Nothing

topIsNot :: Rule Proof
topIsNot = minorRule "top-is-not" f
 where
   f (Var (Not p, Not q)) = Just (Not (Var (p, q)))
   f _ = Nothing -}

{- Strategie voor sterke(?) normalisatie

(prioritering)

1. p \/ q \/ ~p     ~> T           (propageren)
   p /\ q /\ p      ~> p /\ q
   p /\ q /\ ~p     ~> F           (propageren)

2. (p /\ q) \/ ... \/ (p /\ q /\ r)    ~> (p /\ q) \/ ...
         (subset relatie tussen rijtjes: bijzonder geval is gelijke rijtjes)
   p \/ ... \/ (~p /\ q /\ r)  ~> p \/ ... \/ (q /\ r)
         (p is hier een losse variabele)
   ~p \/ ... \/ (p /\ q /\ r)  ~> ~p \/ ... \/ (q /\ r)
         (p is hier een losse variabele)

3. a) elimineren wat aan een kant helemaal niet voorkomt (zie regel hieronder)
   b) rijtjes sorteren
   c) rijtjes aanvullen

Twijfelachtige regel bij stap 3: samennemen in plaats van aanvullen:
   (p /\ q /\ r) \/ ... \/ (~p /\ q /\ r)   ~> q /\ r
          (p is hier een losse variable)
-}

-----------------------------------------------
-- Introduction of var

introduceVar :: Strategy (Context Proof)
introduceVar =  check missing
            <*> use introTrueLeft
            <*> introCompl
            <*> use ruleDistrAnd

missing :: Context Proof -> Bool
missing = isJust . missingVar

localEqVars :: Context Proof -> [ShowString]
localEqVars cp =
   case currentPair cp of
      Just (p, q) -> varsLogic p `union` varsLogic q
      Nothing     -> maybe [] localEqVars (up cp)

missingVar :: Context Proof -> Maybe ShowString
missingVar cp =
   case currentTerm cp >>= fromTerm of
      Just p  -> listToMaybe (localEqVars cp \\ varsLogic p)
      Nothing -> Nothing

introTrueLeft :: Rule SLogic
introTrueLeft = siblingOf groupTrueConjunction $ rewriteRule "IntroTrueLeft" $
   \x -> x  :~>  T :&&: x

introCompl :: Rule (Context Proof)
introCompl = siblingOf groupTrueComplement $ makeRule "IntroCompl" $ \cp -> do
   a <- missingVar cp
   let f = fromTerm >=> fmap toTerm . introTautology a
   changeTerm f cp
 where
   introTautology :: a -> Logic a -> Maybe (Logic a)
   introTautology a T = Just (Var a :||: Not (Var a))
   introTautology a (p :&&: q) = fmap (:&&: q) (introTautology a p)
   introTautology _ _ = Nothing

{-
somewhereDisjunct :: IsStrategy f => f (Context Proof) -> Strategy (Context Proof)
somewhereDisjunct s = oncetd (check isEq <*> layer [] (somewhereOrG s))
 where
   isEq :: Context Proof -> Bool
   isEq cp = (isJust :: Maybe (SLogic, SLogic) -> Bool)
             (currentTerm cp >>= fromTerm :: Maybe (SLogic, SLogic)) -}

somewhereOrG :: IsStrategy g => g (Context a) -> Strategy (Context a)
somewhereOrG = somewhereWhen $ \a -> 
   case currentTerm a >>= (fromTerm :: Term -> Maybe SLogic) of
      Just (_ :||: _) -> False
      _               -> True

-----------------------------------------------------------------------------
-- Inverse rules

inverseRules :: [Rule (Context Proof)]
inverseRules = map use [invDefImpl, invDefEquiv, invDoubleNeg, invIdempOr, invIdempAnd,
   invTrueAnd, invNotTrue, invFalseOr, invNotFalse] ++
   [ invAbsorpOr, invAbsorpAnd, invTrueOr, invComplOr, invFalseAnd
   , invComplAnd, invDistrAnd, invDistrOr]

invDefImpl :: Rule SLogic
invDefImpl = siblingOf groupImplication $ rewriteRule "DefImpl.inv" $
   \x y -> Not x :||: y  :~>  x :->: y

invDefEquiv :: Rule SLogic
invDefEquiv = siblingOf groupEquivalence $ rewriteRule "DefEquiv.inv" $
   \x y -> (x :&&: y) :||: (Not x :&&: Not y)  :~>  x :<->: y

invDoubleNeg :: Rule SLogic
invDoubleNeg = siblingOf groupDoubleNegation $ rewriteRule "NotNot.inv" $
   \x -> x  :~>  Not (Not x)

invIdempOr :: Rule SLogic
invIdempOr = siblingOf groupIdempotency $ rewriteRule "IdempOr.inv" $
   \x -> x  :~>  x :||: x

invIdempAnd :: Rule SLogic
invIdempAnd = siblingOf groupIdempotency $ rewriteRule "IdempAnd.inv" $
   \x -> x :~> x :&&: x

invTrueAnd :: Rule SLogic
invTrueAnd = siblingOf groupTrueConjunction $ rewriteRules "TrueZeroAnd.inv"
   [ \x -> x  :~>  T :&&: x
   , \x -> x  :~>  x :&&: T
   ]

invNotTrue :: Rule SLogic
invNotTrue = siblingOf groupNotTrue $ rewriteRule "NotTrue.inv" $
   F  :~>  Not T

invFalseOr :: Rule SLogic
invFalseOr = siblingOf groupFalseDisjunction $ rewriteRules "FalseZeroOr.inv"
   [ \x -> x  :~>  F :||: x
   , \x -> x  :~>  x :||: F
   ]

invNotFalse :: Rule SLogic
invNotFalse = siblingOf groupNotFalse $ rewriteRule "NotFalse.inv" $
   T  :~> Not F

proofInvRule :: String -> Rule SLogic -> Rule (Context Proof)
proofInvRule = makeInvRuleWithUse (similarity proofExercise)

invAbsorpOr, invAbsorpAnd, invTrueOr, invComplOr, invFalseAnd,
   invComplAnd, invDistrAnd, invDistrOr :: Rule (Context Proof)
invAbsorpOr  = proofInvRule "AbsorpOr.inv" ruleAbsorpOr
invAbsorpAnd = proofInvRule "AbsorpAnd.inv" ruleAbsorpAnd
invTrueOr    = proofInvRule "TrueZeroOr.inv" ruleTrueOr
invComplOr   = proofInvRule "ComplOr.inv" ruleComplOr
invFalseAnd  = proofInvRule "FalseZeroAnd.inv" ruleFalseAnd
invComplAnd  = proofInvRule "ComplAnd.inv" ruleComplAnd
invDistrAnd  = proofInvRule "AndOverOr.inv" ruleDistrAnd -- see GeneralizedRules
invDistrOr   = proofInvRule "OrOverAnd.inv" ruleDistrOr  -- see GeneralizedRules

-----------------------------------------------------------------------------
-- Heuristic

-- Special case: all conjunctions, on both sides, have a common literal.
-- Move this literal to the front (on both sides). Then use inverse distribution
-- (and top-is-and if possible).
commonLiteral :: Strategy (Context Proof)
commonLiteral = 
   repeatS ruleCommonLiteralInFront
   <*>
   repeat1 (somewhere ruleInvDistrCommonLiteral)
--   <*>
--   repeatS (somewhere (use topIsAnd))

findCommonLiteral :: Ord a => (Logic a, Logic a) -> [Logic a]
findCommonLiteral (p, q) = sort $
   intersectList (map conjunctions (disjunctions p ++ disjunctions q))

ruleCommonLiteralInFront :: Rule (Context Proof)
ruleCommonLiteralInFront = siblingOf groupCommutativity $ makeRule "command.common-literal" f
 where
   f :: Context Proof -> [Context Proof]
   f ctx = 
      case currentPair ctx of
         Just eq -> catMaybes $
            [ setCurrentPair x ctx | x <- maybeToList (findInFrontLeft eq) ] ++
            [ setCurrentPair (swap x) ctx | x <- maybeToList (findInFrontLeft (swap eq)) ]
         _ -> []

   findInFrontLeft eq = do
      lit <- listToMaybe (findCommonLiteral eq)
      inFrontLeft lit eq

inFrontLeft :: SLogic -> (SLogic, SLogic) -> Maybe (SLogic, SLogic)
inFrontLeft lit (p, q) = do
   let pss = map (toFront . conjunctions) (disjunctions p)
       toFront = uncurry (++) . partition (==lit)
       new = ors (map ands pss)
   guard (new /= p)
   Just (new, q) 

ruleInvDistrCommonLiteral :: Rule (Context Proof)
ruleInvDistrCommonLiteral = siblingOf groupDistribution $ makeRule "andoveror.inv.common-literal" f
 where
   f ctx =
      case currentPair ctx of
         Just eq ->  catMaybes $
            [ setCurrentPair x ctx | x <- invDistr eq ] ++
            [ setCurrentPair (swap x) ctx | x <- invDistr (swap eq) ] 
         _ -> []

   invDistr eq@(p, q) = do
      guard (not (null (findCommonLiteral eq)))
      new <- applyAll inverseAndOverOr p
      newq <- applyAll inverseAndOverOr q ++[q]
      guard (checkSplit new newq) 
      return (new, q) 

   -- check that after moving common literal to front, the remaing parts are logically equivalent
   checkSplit (a1 :&&: a2) (b1 :&&: b2) = a1 == b1 && eqLogic a2 b2
   checkSplit (a1 :&&: a2) b = a1 == b 
   checkSplit _ _ = False  

intersectList :: Eq a => [[a]] -> [a]
intersectList [] = []
intersectList xs = foldr1 intersect xs

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

----------------------------------------------

-- | Pretty printer with unicode characters
prettyLogic :: SLogic -> String
prettyLogic = rec1
 where
   rec1 p@(_ :&&: _) = recAnd p
   rec1 p@(_ :||: _) = recOr p
   rec1 (p :->: q)   = binop "->" (rec2 p) (rec2 q)
   rec1 (p :<->: q)  = binop "<->" (rec2 p) (rec2 q)
   rec1 p            = rec2 p

   recAnd (p :&&: q) = binop "/\\" (rec2 p) (recAnd q)
   recAnd p          = rec2 p

   recOr (p :||: q) = binop "||" (rec2 p) (recOr q)
   recOr p          = rec2 p

   rec2 (Not p) = "~" ++ rec2 p
   rec2 p       = rec3 p

   -- atoms
   rec3 (Var x) = fromShowString x
   rec3 T       = "T"
   rec3 F       = "F"
   rec3 p       = pars (rec1 p)

   binop op x y = unwords [x, op, y]
   pars s = "(" ++ s ++ ")"