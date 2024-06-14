{-# LANGUAGE RankNTypes, FlexibleInstances #-}
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

module Domain.Logic.Equivalence.ExerciseRP
   ( proofExercise, proofUnicodeExercise
   ) where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import Domain.Logic.BuggyRules
import Domain.Logic.Examples
import Domain.Logic.Formula
import Domain.Logic.Generator
import Domain.Logic.InverseRules hiding (inverseRules)
import Domain.Logic.Parser
import Domain.Logic.Rules
import Domain.Logic.Strategies
import Domain.Logic.Utils
import Domain.Logic.Inductive.RP
import Domain.Logic.NormalForms.Exercises
import Domain.Logic.Equivalence.Data
import Domain.Logic.Equivalence.SplitProof
import Domain.Math.Expr ()
import Ideas.Common.Library
import Ideas.Encoding.Encoder
import Ideas.Common.Strategy.Legacy
import Ideas.Utils.Prelude (ShowString(..), isSubsetOf)
import Prelude hiding ((<*>))

_seeAll :: IO ()
_seeAll = mapM_ _see [0 .. 41]

_see :: Int -> IO ()
_see n = printDerivation proofExercise (examplesAsList proofExercise !! n)

-- Currently, we use the DWA strategy
proofExercise :: Exercise Proof
proofExercise = jsonEncodingProof makeExercise
   { exerciseId     = describe "Prove two propositions equivalent" $
                         propositionalId # "proof-new"
   , status         = Experimental
   , parser         = mapSecond makeProof . parseLogicProof False
   , prettyPrinter  = -- showProof
                      showAsSplitProof
   , equivalence    = withoutContext equivalentProofs
   , similarity     = withoutContext similarProofs
   , suitable       = predicate checkEqForStepsInProof
   , ready          = predicate proofIsReady
   , strategy       = proofStrategy
   , extraRules     = generalAssocProof : 
                      map stepPart (filter ((/= assocId) . getId) extraLogicRules)
                      ++ inverseRules 
                      ++ map stepPart buggyWithoutContext ++ buggyInverseRules
   , ruleOrdering   = ruleOrderingWith [ruleDefImpl, ruleDefEquiv]
   , navigation     = termNavigator
   , examples       = fmap makeProof exampleProofs
   }

proofUnicodeExercise :: Exercise Proof
proofUnicodeExercise = jsonUnicodeEncodingProof proofExercise
   { exerciseId    = describe "Prove two propositions equivalent (unicode support)" $
                        propositionalId # "proof-new.unicode"
   , parser        = mapSecond makeProof . parseLogicProof True
   , prettyPrinter = showProofUnicode
   }

--
assocId :: Id
assocId = getId generalAssocProof

-- associativity, possibly multiple: only recognizer
generalAssocProof :: Rule (Context Proof)
generalAssocProof = addRecognizerBool eq $ setMinor True $ siblingOf groupAssociativity $ makeSimpleRule "assoc" (const Nothing)
 where
   eq old new =
      case (fromContext old, fromContext new) of
         (Just p, Just q) -> 
            case (isOpen p, isOpen q) of 
               (Just (p1, _, p2), Just (q1, _, q2)) -> 
                  (p1 == q1 && p2 /= q2 && equalLogicA p2 q2) ||
                  (p2 == q2 && p1 /= q1 && equalLogicA p1 q1)
               _ -> False
         _ -> False

{-
generalCommutativityProof :: Rule Proof
generalCommutativityProof = addRecognizerBool isCom $ siblingOf groupCommutativity $ makeSimpleRule "comm" (const Nothing)
 where
   isCom (p1, q1) (p2, q2) = 
      equalLogicAC p1 p2 && equalLogicAC q1 q2 &&
      ( (p1 == p2 && not (equalLogicA q1 q2)) || 
        (q1 == q2 && not (equalLogicA p1 p2)))
-}

proofStrategy :: LabeledStrategy (Context Proof)
proofStrategy = label "proof equivalent" $
   repeatS (
          towardsDNF
      ./. (commonLiteralSpecial |> commonLiteral)
      ./. stepPart ruleDistrAnd)
      .*. repeatS ( stepPart comOrReorderSubset
           |> stepPart absorptionOrSubset)
      .*.  normStrategy


{-
   repeatS (
      -- somewhere splitTop
      -- disabled: first investigate how the common subexpressions should be
      -- communicated to the client
      -- |> somewhere commonExprAtom
         splitTop failS
      |> splitTop (useC towardsDNF)
      |> splitTop (commonLiteralSpecial |> commonLiteral)
      |> somewhere (check (not . isSplit) <*> toStrategy (useC distrAnd))
      ) -}

commonLiteralSpecial :: Strategy (Context Proof)
commonLiteralSpecial =
   repeatS (stepPairDir ruleCommonLiteralSpecialInFront)
   <*>
   repeat1 (stepPairDir ruleInvDistrCommonLiteral)
--   <*>
--  repeatS (somewhere topIsAnd)

ruleCommonLiteralSpecialInFront :: Direction -> Rule (SLogic, SLogic)
ruleCommonLiteralSpecialInFront dir = siblingOf groupCommutativity $ makeListRule "command.common-literal-special" f
 where
   f :: (SLogic, SLogic) -> [(SLogic, SLogic)]
   f eq =
      [ x | dir == BottomUp, x <- maybeToList (findInFrontLeft eq) ] ++
      [ swap x | dir == TopDown, x <- maybeToList (findInFrontLeft (swap eq)) ]

   findInFrontLeft eq@(p1 :&&: p2, q)
      | isAtomic p1 && isDNF p2 && all (`notElem` varsLogic p2) (varsLogic p1) && isDNF q = do
           lit <- listToMaybe (findCommonLiteral (p1, q))
           res <- inFrontLeft lit (swap eq)
           return (swap res)
   findInFrontLeft _ = Nothing

commonLiteral :: Strategy (Context Proof)
commonLiteral = 
   repeatS (stepPairDir ruleCommonLiteralInFront)
   <*>
   repeat1 (stepPairDir ruleInvDistrCommonLiteral)

findCommonLiteral :: Ord a => (Logic a, Logic a) -> [Logic a]
findCommonLiteral (p, q) = sort $
   intersectList (map conjunctions (disjunctions p ++ disjunctions q))

ruleCommonLiteralInFront :: Direction -> Rule (SLogic, SLogic)
ruleCommonLiteralInFront dir = siblingOf groupCommutativity $ makeListRule "command.common-literal" f
 where
   f :: (SLogic, SLogic) -> [(SLogic, SLogic)]
   f eq = 
      [ x | dir == TopDown, x <- maybeToList (findInFrontLeft eq) ] ++
      [ swap x | dir == BottomUp, x <- maybeToList (findInFrontLeft (swap eq)) ]

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
    (  introduceVar 
   .|. (stepPart comOrReorderSubset |> stepPart absorptionOrSubset)
   .|. stepPart ruleIdempOr
    ) |>
    (  liftPairRule TopDown  comOrReorder
   .|. liftPairRule BottomUp comOrReorder
   .|. liftPairRule TopDown  comAndReorder 
   .|. liftPairRule BottomUp comAndReorder
   .|. stepPart comAndReorderEquiv
    )

{- repeatS $
   splitTop (somewhere (
         use ruleIdempOr   <|>
         use ruleIdempAnd  <|>
         use absorptionOrSubset <|>
         use ruleComplOr
      ))
   |> splitTop (somewhereOrG introduceVar) -}

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

-- ruleFalseOr, ruleTrueOr, ruleIdempOr, ruleAbsorpOr, ruleComplOr

towardsDNF :: Strategy (Context Proof)
towardsDNF =  choice (map stepPart 
   [ruleIdempOr
   , ruleIdempAnd, ruleAbsorpOr, ruleAbsorpAnd, ruleComplOr, ruleComplAnd
   , ruleFalseOr, ruleTrueOr, ruleFalseAnd, ruleTrueAnd
   ]) 
   ./.
   choice (map stepPart
   [ruleDoubleNeg, ruleNotTrue, ruleNotFalse
   ]) 
   ./.
   ( stepPart specialDeMorganNotProof .|.
   (stepPart groupLiteralsOr   .*. choice (map stepPart 
   [ruleIdempOr, ruleComplOr]) .*. try (stepPart ruleTrueOr)
   .|. stepPart groupLiteralsAnd.*. choice (map stepPart 
   [ruleIdempAnd, ruleComplAnd]) .*. try (stepPart ruleFalseAnd)))
   ./. choice (map stepPart 
   [ ruleDefImpl, ruleDefEquiv, ruleDeMorganAnd, ruleDeMorganOr
   ])
--   ./. choice (map stepPart 
--   [  ruleDistrAnd
--   ])
   <|> (liftPairRule TopDown comOrForSplit .*. try (liftPairRule BottomUp comOrForSplit))
   <|> (liftPairRule TopDown comAndForSplit .*. try (liftPairRule BottomUp comAndForSplit))
   <|> liftPairRule BottomUp comOrForSplit
   <|> liftPairRule BottomUp comAndForSplit
   ./.
   (stepPart groupLiteralsOr .|. stepPart groupLiteralsAnd)
   .|. stepPart specialDistrNotRule     -- deze laatste hoort eigenlijk in de proofstrategy
  

  {- (stepPart groupLiteralsOr   .*. choice (map stepPart 
   [ruleIdempAnd, ruleComplAnd]) .*. try (stepPart ruleFalseAnd)
   .|. stepPart groupLiteralsAnd.*. choice (map stepPart 
   [ruleIdempOr, ruleComplOr]) .*. try (stepPart ruleTrueOr)) -}

liftPairRule :: Direction -> (Direction -> Rule (SLogic, SLogic)) -> Rule (Context Proof)
liftPairRule dir f = makeRule (getId r) $ applyAll $ 
   case dir of
      TopDown  -> stepTD (showId r) .*. somePart (liftPair r)
      BottomUp -> stepBU (showId r) .*. somePart (liftPair r)
 where
   r = f dir

-- als minstens 1 van de disjuncten (of conjuncten) een negatie bevat, dan krijgt
-- de DeMorgan regel een hogere prioriteit
specialDeMorganNotProof :: Rule SLogic
specialDeMorganNotProof = siblingOf groupDeMorgan $ makeSimpleRule "specialdemorgan" f
 where
   f (Not p) | length xs > 1 && any notComposed xs = 
      Just $ ands $ map Not xs
    where
      xs = disjunctions p
   f (Not p) | length xs > 1 && any notComposed xs = 
      Just $ ors $ map Not xs
    where
      xs = conjunctions p
   f _ = Nothing 

   notComposed (Not (Var _)) = False
   notComposed (Not _)       = True
   notComposed _             = False

specialDistrNot1 :: Strategy SLogic  -- zonder context, kan waarschijnlijk anders opgelost?
specialDistrNot1 =
   (check condOr  <*> ruleDistrOr) <|>
   (check condAnd <*> ruleDistrAnd)
 where
    condOr (p :||: q) = cond conjunctions p q
    condOr _          = False

    condAnd (p :&&: q) = cond disjunctions p q
    condAnd _          = False

    cond f p q = (p `negatedIn` qs && length qs == 2) ||
                 (q `negatedIn` ps && length ps == 2)
     where
        ps = f p
        qs = f q

    negatedIn (Not x) xs = x `elem` xs || (Not (Not x) `elem` xs)
    negatedIn x xs       = Not x `elem` xs

specialDistrNotRule :: Rule SLogic
specialDistrNotRule = siblingOf groupDistribution $ makeListRule "specialDistrNotR" (applyAll specialDistrNot1)  

comOrForSplit :: Direction -> Rule (SLogic, SLogic)
comOrForSplit dir = makeListRule "top-is-or.com" $ \pair ->
   let checkDirection new
          | dir == TopDown = snd pair == snd new
          | otherwise      = fst pair == fst new
   in sortBy compareEqual $ filter checkDirection (acTopRuleFor True (collect orView) pair)

comAndForSplit :: Direction -> Rule (SLogic, SLogic)
comAndForSplit dir = makeListRule "top-is-and.com" $ \pair ->
   let checkDirection new
          | dir == TopDown = snd pair == snd new
          | otherwise      = fst pair == fst new
   in sortBy compareEqual $ filter checkDirection (acTopRuleFor True (collect andView) pair)

comOrReorder :: Direction -> Rule (SLogic, SLogic)
comOrReorder TopDown  = comOrReorderTD
comOrReorder BottomUp = comOrReorderBU

comOrReorderTD :: Rule (SLogic, SLogic) -- only top-down
comOrReorderTD = makeSimpleRule "top-is-or.com" $ \(lhs, rhs) ->
   let xs  = disjunctions lhs
       ys  = disjunctions rhs
       new = ors (rec xs ys)
   in if equalLogicA lhs new then Nothing else Just (new, rhs)
 where
   rec xs [] = xs
   rec xs (y:ys) = 
      let (xs1, xs2) = partition (eqLogic y) xs
      in xs1 ++ rec xs2 ys

comOrReorderBU :: Rule (SLogic, SLogic) -- only bottomup
comOrReorderBU = makeListRule "top-is-or.com" $ 
   map swap . applyAll comOrReorderTD . swap

comAndReorder :: Direction -> Rule (SLogic, SLogic)
comAndReorder TopDown  = comAndReorderTD
comAndReorder BottomUp = comAndReorderBU

comAndReorderTD :: Rule (SLogic, SLogic) -- only top-down
comAndReorderTD = makeSimpleRule "top-is-and.com" $ \(lhs, rhs) ->
   let xs  = conjunctions lhs
       ys  = conjunctions rhs
       new = ands (rec xs ys)
   in if equalLogicA lhs new then Nothing else Just (new, rhs)
 where
   rec xs [] = xs
   rec xs (y:ys) = 
      let (xs1, xs2) = partition (eqLogic y) xs
      in xs1 ++ rec xs2 ys

comAndReorderBU :: Rule (SLogic, SLogic) -- only bottomup
comAndReorderBU = makeListRule "top-is-and.com" $ 
   map swap . applyAll comAndReorderTD . swap

comAndReorderEquiv :: Rule SLogic
comAndReorderEquiv = makeSimpleRule "and.com" $ \p -> 
   rec (disjunctions p)
 where
   rec (p:q:rest) | not (equalLogicA p q) && sort ps == sort qs = Just (ors (p:p:rest))
    where
      ps = conjunctions p
      qs = conjunctions q
   rec (p:rest) = (p :||:) <$> rec rest
   rec [] = Nothing

comOrReorderSubset :: Rule SLogic
comOrReorderSubset = makeSimpleRule "or.com" $ \p ->
   let xs  = disjunctions p
       new = ors  $ f xs
   in if equalLogicA p new then Nothing else Just new
 where
   f [] = []
   f (x:xs) = let (xs1, xs2) = partition (isSubConjunctionsOf x) xs
      in (x:xs1) ++ f xs2

 --     (fst (partition (isSubConjunctionsOf x) (f xs))) ++ (snd (partition (isSubConjunctionsOf x) (f xs)) )
   isSubConjunctionsOf y z = isSubsetOf (conjunctions y) (conjunctions z) || isSubsetOf (conjunctions z) (conjunctions y) 


compareEqual :: Eq a => (a, a) -> (a, a) -> Ordering
compareEqual (x, y) (a, b) = (a == b) `compare` (x == y)

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
introduceVar =  liftPair (check missing)
            <*> (liftPairRule TopDown introTrueLeft .|. liftPairRule BottomUp introTrueLeft)
            <*> (liftPairRule TopDown introCompl .|. liftPairRule BottomUp introCompl)
            <*> stepPart ruleDistrAnd
 
missing :: (SLogic, SLogic) -> Bool
missing eq = not $ null (missingVarLeft eq ++ missingVarRight eq)

missingVarLeft ::(SLogic, SLogic) -> [ShowString]
missingVarLeft (p, q) = nub (concatMap f (disjunctions p))
 where
   f x = filter (not . isSpecial) (varsLogic q \\ varsLogic x)

   -- in SplitProof, atomic parts are searched for and replaced by vars
   -- These vars (digits only) should not be introduced here
   isSpecial = all isDigit . fromShowString

missingVarRight :: (SLogic, SLogic) -> [ShowString]
missingVarRight = missingVarLeft . swap

introTrueFunction :: [ShowString] -> [SLogic] -> SLogic -> [SLogic]
introTrueFunction as otherSide = introTrueList . disjunctions
 where 
   introTrueList [] = []
   introTrueList (x:xs) =  
      [ ors ((T :&&: x) : xs)
      | all (not . equalLogicAC x) otherSide
      , a <- as
      , a `notElem` varsLogic x
      ] ++  map (x :||:) (introTrueList xs)

introTrueLeft :: Direction -> Rule (SLogic, SLogic)
introTrueLeft TopDown  = introTrueLeftTD
introTrueLeft BottomUp = introTrueLeftBU

introTrueLeftTD :: Rule (SLogic, SLogic)
introTrueLeftTD = siblingOf groupTrueConjunction $ makeListRule "TrueZeroAnd.inv" f
  where
   f eq@(p, q) = [ (newp, q) | newp <- introTrueFunction (missingVarLeft eq) (disjunctions q) p ]
                     
introTrueLeftBU :: Rule (SLogic, SLogic)
introTrueLeftBU = siblingOf groupTrueConjunction $ makeListRule "TrueZeroAnd.inv" f
  where
   f eq@(p, q) = [ (p, newq) | newq <- introTrueFunction (missingVarRight eq) (disjunctions p) q ]
 
introComplFunction :: [ShowString] -> SLogic -> [SLogic]
introComplFunction as = introComplList . disjunctions
 where 
   introComplList ((T :&&: x):xs) = 
      [ ors (((Var a :||: Not (Var a)) :&&: x) : xs)
      | a <- as
      , a `notElem` varsLogic x
      ] 
   introComplList (x:xs) =  map (x :||:) (introComplList xs)
   introComplList [] = []

introCompl :: Direction -> Rule  (SLogic, SLogic)
introCompl TopDown  = introComplTD
introCompl BottomUp = introComplBU

introComplTD :: Rule  (SLogic, SLogic)
introComplTD = siblingOf groupTrueConjunction $ makeRule "logic.propositional.ComplOr.inv" f
  where
   f eq@(p,q) = [ (newp, q) | newp <- introComplFunction (missingVarLeft eq) p]

introComplBU :: Rule  (SLogic, SLogic)
introComplBU = siblingOf groupTrueConjunction $ makeRule "logic.propositional.ComplOr.inv" f
  where
   f eq@(p, q) = [(p, newq) | newq <- introComplFunction (missingVarRight eq) q]
{- 
introCompl :: Rule (Environment, (SLogic, SLogic))
introCompl = siblingOf groupTrueComplement $ makeRule "IntroCompl" f
  where
   f (env,(p,q)) = [(env, (fromJust $ introTautology a p, q)), a <-  missingVar (env,(p,q)) ]
--   changeTerm f cp

   introTautology :: a -> Logic a -> Maybe (Logic a)
   introTautology a T = Just (Var a :||: Not (Var a))
   introTautology a (p :&&: q) = fmap (:&&: q) (introTautology a p)
   introTautology _ _ = Nothing


somewhereDisjunct :: IsStrategy f => f (Context Proof) -> Strategy (Context Proof)
somewhereDisjunct s = oncetd (check isEq <*> layer [] (somewhereOrG s))
 where
   isEq :: Context Proof -> Bool
   isEq cp = (isJust :: Maybe (SLogic, SLogic) -> Bool)
             (currentTerm cp >>= fromTerm :: Maybe (SLogic, SLogic))

somewhereOrG :: IsStrategy g => g (Context a) -> Strategy (Context a)
somewhereOrG = somewhereWhen $ \a -> 
   case currentTerm a >>= (fromTerm :: Term -> Maybe SLogic) of
      Just (_ :||: _) -> False
      _               -> True -}

-----------------------------------------------------------------------------
-- Inverse rules

inverseRules :: [Rule (Context Proof)]
inverseRules = map stepPart [invDefImpl, invDefEquiv, invDoubleNeg, invIdempOr, invIdempAnd,
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
proofInvRule name r = addRecognizerBool eqCtx $ setSiblings $ setBuggy (isBuggy r) $ makeRule name (const Nothing)
 where
   setSiblings n = foldr siblingOf n (ruleSiblings r)
   eqCtx a b = 
      case (fromContext a >>= isOpen, fromContext b >>= isOpen) of 
         (Just (a1, _, a2), Just (b1, _, b2)) 
            | a1 == b1 -> eq a2 b2
            | a2 == b2 -> eq a1 b1
         _ -> False

   eq a b = any (equalLogicA a) $ applyAll (sw r) b

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
buggyInvAndCompl  = proofInvRule "logic.propositional.buggy.AndCompl.inv" buggyAndCompl
buggyInvOrCompl   = proofInvRule "logic.propositional.buggy.OrCompl.inv" buggyOrCompl
buggyInvTrueProp  = proofInvRule "logic.propositional.buggy.TrueProp.inv" buggyTrueProp
buggyInvFalseProp = proofInvRule "logic.propositional.buggy.FalseProp.inv" buggyFalseProp

buggyInverseRules :: [Rule (Context Proof)]
buggyInverseRules = [ buggyInvAndCompl, buggyInvOrCompl, buggyInvTrueProp, buggyInvFalseProp ]

-----------------------------------------------------------------------------
-- Heuristic

-- Special case: all conjunctions, on both sides, have a common literal.
-- Move this literal to the front (on both sides). Then use inverse distribution
-- (and top-is-and if possible).
{- 
commonLiteral :: Strategy (Context Proof)
commonLiteral = 
   repeatS ruleCommonLiteralInFront
   <*>
   repeat1 (somewhere ruleInvDistrCommonLiteral)
--   <*>
--   repeatS (somewhere (use topIsAnd))
-}



ruleInvDistrCommonLiteral :: Direction -> Rule (SLogic, SLogic)
ruleInvDistrCommonLiteral dir = siblingOf groupDistribution $ makeListRule "andoveror.inv.common-literal" f
 where
   f :: (SLogic, SLogic) -> [(SLogic, SLogic)]
   f eq = 
      [ x | dir == TopDown, x <- invDistr eq ] ++
      [ swap x | dir == BottomUp, x <- invDistr (swap eq) ]

   invDistr eq@(p, q) = do
      guard (not (null (findCommonLiteral eq)))
      new <- applyAll inverseAndOverOr p
      newq <- applyAll inverseAndOverOr q ++[q]
      guard (checkSplit new newq) 
      return (new, q) 

   -- check that after moving common literal to front, the remaing parts are logically equivalent
   checkSplit (a1 :&&: a2) (b1 :&&: b2) = a1 == b1 && eqLogic a2 b2
   checkSplit (a1 :&&: _) b = a1 == b 
   checkSplit _ _ = False  

intersectList :: Eq a => [[a]] -> [a]
intersectList [] = []
intersectList xs = foldr1 intersect xs

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
{-
for testing
buggyStrat :: LabeledStrategy (Context Proof)
buggyStrat = label "buggyproof equivalent" $ choice (map stepPart buggyWithoutContext)
-}
 --