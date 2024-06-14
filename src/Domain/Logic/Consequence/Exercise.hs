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

module Domain.Logic.Consequence.Exercise (consequenceExercise) where

import Control.Monad
import Data.Function (on)
import Data.List hiding (singleton)
import Data.Maybe
import Domain.Logic.Formula
import Domain.Logic.Generator (equalLogicA, normalizeLogicA)
import Domain.Logic.Parser
import Domain.Logic.Rules
import Domain.Logic.Strategies (cnfStrategy)
import Domain.Logic.Utils
import Domain.Math.Expr ()
import Ideas.Common.Library hiding (singleton, traverse)
import Ideas.Common.Strategy.Legacy
import Ideas.Common.Rewriting.AC
import Ideas.Common.Traversal.Navigator
import Ideas.Utils.Prelude
import Prelude hiding ((<*>))

consequenceExercise :: Exercise Proof
consequenceExercise = makeExercise
   { exerciseId     = describe "Prove that formula is a logical consequence of a set of formulas" $
                         propositionalId # "consequence"
   , status         = Experimental
   , parser         = mapSecond makeProof . parseConsequence False
   , prettyPrinter  = showProof
   , equivalence    = equivalentProofs
   , similarity     = similarProofs
   , suitable       = predicate suitableProof
   , ready          = predicate readyProof
   , strategy       = proofStrategy
--   , extraRules     = map use extraLogicRules ++ map use buggyRules
   , navigation     = termNavigator
   , examples       = exampleProofs
   }

-- (assumptions, consequence)
type Proof = Logic ([SLogic], SLogic)

makeProof :: ([SLogic], SLogic) -> Proof
makeProof = Var

proofPair :: Proof -> ([SLogic], SLogic)
proofPair x = (map catLogic $ traverse fst x, catLogic (fmap snd x))

initial :: Ref Term
initial = makeRef "initial"

onAssumption :: (IsStrategy f, Navigator a) => f a -> Strategy a
onAssumption s = ruleDown <*> ruleDown <*> s <*> ruleUp <*> ruleUp

onConsequence :: (IsStrategy f, Navigator a) => f a -> Strategy a
onConsequence s = ruleDownLast <*> s <*> ruleUp

getInitial :: Context Proof -> Maybe [SLogic]
getInitial ctx =
   ((initial ? ctx) >>= fromTerm)
    `mplus`
   fmap (fst . proofPair) (fromContext ctx)

showProof :: Proof -> String
showProof proof =
   let (ps, q) = proofPair proof
   in intercalate ", " (map show ps) ++ " => " ++ show q

equivalentProofs :: Context Proof -> Context Proof -> Bool
equivalentProofs c1 c2 = fromMaybe False $ do
   as1     <- getInitial c1
   as2     <- getInitial c2
   (ps, p) <- fmap proofPair (fromContext c1)
   (qs, q) <- fmap proofPair (fromContext c2)
   return $ ands as1 === ands as2
         && ands as1 ==> ands ps
         && ands as2 ==> ands qs
         && (ands ps :->: p) <=> (ands qs :->: q)
         && p === q

similarProofs :: Context Proof -> Context Proof -> Bool
similarProofs c1 c2 = fromMaybe False $ do
   as1     <- getInitial c1
   as2     <- getInitial c2
   (ps, p) <- fmap proofPair (fromContext c1)
   (qs, q) <- fmap proofPair (fromContext c2)
   let f = sort . map normalizeLogicA
   return $ as1 == as2
         && f ps == f qs
         && equalLogicA p q

suitableProof :: Proof -> Bool
suitableProof proof =
   let (ps, p) = proofPair proof
   in ands ps ==> p && p `notElem` ps

readyProof :: Proof -> Bool
readyProof proof =
   case proofPair proof of
      ([p], q) -> equalLogicA p q
      _ -> False

readyProofC :: Context Proof -> Bool
readyProofC = maybe False readyProof . fromContext

proofStrategy :: LabeledStrategy (Context Proof)
proofStrategy = label "consequence" $
   keepInitialAssumptions
   <*> try (use conjIntro)
       -- use cnf for the (singleton) assumption
   <*> repeatS (somewhere splitTop)
   <*> onAssumption (useC cnfStrategy)
       -- use cnf for the consequence
   <*> onConsequence (useC cnfStrategy)
       -- strong normalization of assumption and consequence
   <*> repeatS (somewhere (use absorptionAndSubset <|> use fakeAbsorption <|> use fakeAbsorptionNot))
   <*> repeatS (somewhere splitTop)
   <*> use checkCNF <*> normStrategy
 where
   splitTop = use topIsAnd |> use topIsAndCom

checkCNF :: Rule Proof
checkCNF = minor $ makeRule "is-cnf" $ \proof -> do
   let (ps, p) = proofPair proof
   guard (length ps == 1 && isCNF (head ps) && isCNF p)
   Just proof

-- strong normalization for CNF
normStrategy :: Strategy (Context Proof)
normStrategy = untilS readyProofC $
      use assumptionIsFalse
   |> use conjElim
   |> use comAndSubset
   |> somewhere (use ruleFalseAnd <|> use ruleTrueOr)
   |> somewhere (
         use ruleIdempOr   <|>
         use ruleIdempAnd  <|>
         use ruleComplOr   <|>
         use absorptionAndSubset <|>
         use ruleDistrOr   <|>
         use ruleTrueAnd
      )
   |> oncetd (use sortRuleOr)
   |> oncetd (use sortRuleAnd)
   -- |> oncetd eliminateVar
   |> somewhereConjunct introduceVar

sortRuleOr :: Rule SLogic
sortRuleOr = ruleTrans "CommOr.sort" $
   sortRuleBy compareVar $ disjunctions <-> ors

sortRuleAnd :: Rule SLogic
sortRuleAnd = ruleTrans "CommAnd.sort" $
   sortRuleBy compareVar $ conjunctions <-> ands

sortRuleBy :: (b -> b -> Ordering) -> View a [b] -> Transformation a
sortRuleBy cmp v = makeTrans $ \p -> do
   xs <- match v p
   guard (not (sortedBy cmp xs))
   let ys = sortBy cmp xs
   return (build v ys)

sortedBy :: (a -> a -> Ordering) -> [a] -> Bool
sortedBy cmp = rec
 where
   rec (x:y:zs) = cmp x y /= GT && rec (y:zs)
   rec _        = True

compareVar :: Ord a => Logic a -> Logic a -> Ordering
compareVar = compare `on` (\x -> (varsLogic x, x))

keepInitialAssumptions :: Rule (Context Proof)
keepInitialAssumptions = minorRule "initial" $ \ctx -> do
   (ps, _) <- fmap proofPair (fromContext ctx)
   Just $ insertRef initial (toTerm ps) ctx

assumptionIsFalse :: Rule Proof
assumptionIsFalse = makeRule "assump-false" $ \proof ->
   case proofPair proof of
      ([F], q) -> Just (makeProof ([F :&&: q], q))
      _        -> Nothing

comAndSubset :: Rule Proof
comAndSubset = makeRule "command-subset" $ \proof -> do
   let (ps, q) = proofPair proof
   p <- singleton ps
   let cps = conjunctions p
       cqs = conjunctions q
       (cps1, cps2) = partition (\x -> any (equalLogicA x) cqs) cps
   guard (p /= q && cps /= (cqs++cps2))
   guard (all (\x -> any (equalLogicA x) cps1) cqs)
   Just (makeProof ([ands (cqs++cps2)], q))

conjElim :: Rule Proof
conjElim = makeRule "conj-elim" $ \proof -> do
   let (ps, q) = proofPair proof
   p <- singleton ps
   let cps = conjunctions p
       cqs = conjunctions q
   guard (p /= q && ( isPrefixOfWith equalLogicA cqs cps
                   || isSuffixOfWith equalLogicA cqs cps))
   Just (makeProof ([q], q))

conjIntro :: Rule Proof
conjIntro = makeRule "conj-intro" (f . proofPair)
 where
   f (ps, q) | length ps > 1 =
      Just (makeProof ([ands ps], q))
   f _ = Nothing

-- eliminate a variable in the assumption
{-
eliminateVar :: Strategy (Context Proof)
eliminateVar =  check superfluous
            <*> (liftToContext $ makeRule "jippie" (\_ -> Just $ makeProof ([pp], pp)))
 where
   pp = Var (ShowString "b")

superfluous :: Context Proof -> Bool
superfluous = isJust . superfluousVar

superfluousVar :: Context Proof -> Maybe ShowString
superfluousVar cp =
   case currentTerm cp >>= fromTerm of
      Just (ps, q) -> listToMaybe (nub (concatMap varsLogic ps) \\ varsLogic q)
      _ -> Nothing -}

introduceVar :: Strategy (Context Proof)
introduceVar =  check missing
            <*> use introFalseLeft
            <*> introCompl

missing :: Context Proof -> Bool
missing = isJust . missingVar

-- The variables in the current subproof
globalVars :: Context Proof -> [ShowString]
globalVars cp =
   case currentTerm cp >>= fromTerm of
      Just (ps, q) -> nub (concatMap varsLogic (q:ps))
      _ -> maybe [] globalVars (up cp)

missingVar :: Context Proof -> Maybe ShowString
missingVar cp =
   case currentTerm cp >>= fromTerm of
      Just p  -> listToMaybe (globalVars cp \\ varsLogic p)
      Nothing -> Nothing

introFalseLeft :: Rule SLogic
introFalseLeft = rewriteRule "IntroFalseLeft" $
   \x -> x  :~>  F :||: x

introCompl :: Rule (Context Proof)
introCompl = makeRule "IntroCompl" $ \cp -> do
   a <- missingVar cp -- focus is on conjunct
   let f = fromTerm >=> fmap toTerm . introContradiction a
   changeTerm f cp
 where
   introContradiction :: a -> Logic a -> Maybe (Logic a)
   introContradiction a F = Just (Var a :&&: Not (Var a))
   introContradiction a (p :||: q) =
      fmap (:||: q) (introContradiction a p) `mplus`
      fmap (p :||:) (introContradiction a q)
   introContradiction _ _ = Nothing

topIsAnd :: Rule Proof
topIsAnd = minor $
   ruleTrans "top-is-and" $ acTopRuleFor False (collect andView)

topIsAndCom :: Rule Proof
topIsAndCom = ruleTrans "top-is-and.com" $ acTopRuleFor True (collect andView)

acTopRuleFor :: Bool -> (forall a . Isomorphism (Logic a) [Logic a])
             -> Transformation Proof
acTopRuleFor com ep = makeTrans $ \proof -> do
   (ps, q) <- maybeToList (getSingleton proof)
   guard (length ps == 1)
   let pair = (head ps, q)
       pairings = if com then pairingsAC else pairingsA
       ep2 = ep *** ep
       (xs, ys) = from ep2 pair
   guard (length xs > 1 && length ys > 1)
   zs <- fmap (map (to ep2)) (pairings False xs ys)
   guard (all (uncurry (==>)) zs)
   return (to ep [ Var ([x], y) | (x, y) <- zs])

-- see somewhereDisjunct in Proofs
somewhereConjunct :: IsStrategy f => f (Context Proof) -> Strategy (Context Proof)
somewhereConjunct s = somewhere (check isPair <*> onPair)
 where
   isPair ctx = case currentTerm ctx of
                   Just (TList [_, _]) -> True
                   _ -> False
   onPair =
          onAssumption  (somewhereAndG s) -- conjunct in assumption
      <|> onConsequence (somewhereAndG s) -- conjunct in consequence

somewhereAndG :: IsStrategy g => g (Context a) -> Strategy (Context a)
somewhereAndG = somewhereWhen $ \a -> 
   case currentTerm a >>= (fromTerm :: Term -> Maybe SLogic) of
      Just (_ :&&: _) -> False
      _               -> True

exampleProofs :: Examples Proof
exampleProofs = examplesWithDifficulty
   [ easy      [p :&&: Not p] q
   , medium    [p :->: q, p :->: Not q] (Not p)
   , medium    [Not p :->: Not q, q] p
   , difficult [p :->: q, r :->: s] ((p :&&: r) :->: (q :&&: s))
   , difficult [Not r :<->: q] (p :->: (q :||: r))
   , medium    [p :->: q, p :->: r] (p :->: (q :&&: r))
   , medium    [p :->: q, q :->: r] (p :->: r)
   , medium    [p :->: (q :->: r), q] (p :->: r)
   -- , medium    [p :->: (q :->: p)] p
   , difficult [p :->: (q :&&: r)] ((p :&&: q) :<->: (p :&&: r))
   , difficult [p :<->: r, q :<->: s] ((p :->: q) :<->: (r :->: s))
   , difficult [p :<->: r, q :<->: s] ((p :&&: q) :<->: (r :&&: s))
   , difficult [p :<->: r, q :<->: s] ((p :||: q) :<->: (r :||: s))
   , difficult [q :<->: s] ((p :&&: q) :<->: (p :&&: s))
   , easy      [p :->: (p :->: q), p] q
   , easy      [p :->: q, p] q
   , easy      [p :||: (q :&&:r)] (Not p :->: r)
   , easy      [p :->: q, Not q] (Not p)
   , difficult [q] ((p :&&: q) :<->: p)
   , difficult [Not q] ((p :||: q) :<->: p)
   , difficult [p :<->: q, p] q
   , difficult [p :<->: q, Not p] (Not q)
   , medium    [q] (p :->: (p :&&:q))
   , medium    [Not q] ((p :||: q) :->: p)
   , medium    [Not q, p :||: q] p
   ]
 where
   easy      = make Easy
   medium    = make Medium
   difficult = make Difficult

   make dif ps consq = (dif, makeProof (ps, consq))

   p = Var (ShowString "p")
   q = Var (ShowString "q")
   s = Var (ShowString "s")
   r = Var (ShowString "r")

isPrefixOfWith, isSuffixOfWith :: (a -> a -> Bool) -> [a] -> [a] -> Bool
isPrefixOfWith _ [] _ = True
isPrefixOfWith _ _ [] = False
isPrefixOfWith eq (x:xs) (y:ys) = eq x y && isPrefixOfWith eq xs ys

isSuffixOfWith eq xs ys = isPrefixOfWith eq (reverse xs) (reverse ys)

singleton :: [a] -> Maybe a
singleton [x] = Just x
singleton _   = Nothing

-- debug
{-
vb :: Proof
Right vb = parseConsequence False "p -> q, r -> s => \
    \(~p || q || ~r || s) /\\ (~p || q || ~r || ~s) /\\ (~p || ~q || ~r || s) /\\ (p || q || ~r || s) =>\
    \(~p || q || ~r || s) /\\ (~p || q || ~r || ~s) /\\ (~p || q || ~r || s)"
-}

-- (p \/ q) /\ ... /\ (p \/ q \/ r)    ~> (p \/ q) /\ ...
--    (subset relatie tussen rijtjes: bijzonder geval is gelijke rijtjes)
absorptionAndSubset :: Rule SLogic
absorptionAndSubset = ruleList "absorpand-subset" $ \p -> do
   let xss = map disjunctions (conjunctions p)
       yss = nub $ filter (\xs -> all (ok xs) xss) xss
       ok xs ys = not (ys `isSubsetOf` xs) || xs == ys
   guard (length yss < length xss)
   return $ ands (map ors yss)

-- p /\ ... /\ (~p \/ q \/ r)  ~> p /\ ... /\ (q \/ r)
--    (p is hier een losse variabele)
fakeAbsorption :: Rule SLogic
fakeAbsorption = makeRule "fakeAbsorption" $ \p -> do
   let xs = conjunctions p
   v <- [ a | a@(Var _) <- xs ]
   let ys  = map (ors . filter (/= Not v) . disjunctions) xs
       new = ands ys
   guard (p /= new)
   return new

-- ~p /\ ... /\ (p \/ q \/ r)  ~> ~p /\ ... /\ (q \/ r)
--   (p is hier een losse variabele)
fakeAbsorptionNot :: Rule SLogic
fakeAbsorptionNot = makeRule "fakeAbsorptionNot" $ \p -> do
   let xs = conjunctions p
   v <- [ a | Not a@(Var _) <- xs ]
   let ys  = map (ors . filter (/= v) . disjunctions) xs
       new = ands ys
   guard (p /= new)
   return new