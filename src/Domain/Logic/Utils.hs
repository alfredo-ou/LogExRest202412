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
-- Utilities for the logic domain
--
-----------------------------------------------------------------------------

module Domain.Logic.Utils
   ( propositionalId, makeSimpleRule, makeListRule
     -- groups of rules
   , groupAbsorption, groupAssociativity, groupCommutativity, groupDeMorgan
   , groupDistribution, groupIdempotency
   , groupDoubleNegation, groupEquivalence, groupFalseComplement
   , groupFalseConjunction, groupFalseDisjunction, groupNotTrue
   , groupImplication, groupTrueComplement, groupTrueConjunction
   , groupTrueDisjunction, groupNotFalse
     -- other utility functions
   , makeInvRule, makeInvRuleWithUse
   , collect, andView, orView, eqView
   , somewhereOr, somewhereAnd
   , (===), (==>), (<=>)
   ) where

import Data.Maybe
import Domain.Logic.Formula
import Ideas.Common.Library

propositionalId :: Id
propositionalId = newId "logic.propositional"

makeListRule :: String -> (a -> [a]) -> Rule a
makeListRule s = makeRule (propositionalId # s)

makeSimpleRule :: String -> (a -> Maybe a) -> Rule a
makeSimpleRule s = makeRule (propositionalId # s)

-----------------------------------------------------------------------------
-- Groups of rules

groupAbsorption, groupAssociativity, groupCommutativity, groupDeMorgan,
   groupDistribution, groupIdempotency :: Id
groupAbsorption    = makeGroup "Absorption"
groupAssociativity = makeGroup "Associativity"
groupCommutativity = makeGroup "Commutativity"
groupDeMorgan      = makeGroup "DeMorgan"
groupDistribution  = makeGroup "Distribution"
groupIdempotency   = makeGroup "Idempotency"

groupDoubleNegation, groupEquivalence, groupFalseComplement,
   groupFalseConjunction, groupFalseDisjunction, groupNotTrue,
   groupImplication, groupTrueComplement, groupTrueConjunction,
   groupTrueDisjunction, groupNotFalse :: Id
groupDoubleNegation   = makeGroup "doublenegation"
groupEquivalence      = makeGroup "equivalence"
groupFalseComplement  = makeGroup "falsecomplement"
groupFalseConjunction = makeGroup "falseconjunction"
groupFalseDisjunction = makeGroup "falsedisjunction"
groupNotTrue          = makeGroup "group-nottrue"
groupImplication      = makeGroup "implication"
groupTrueComplement   = makeGroup "truecomplement"
groupTrueConjunction  = makeGroup "trueconjunction"
groupTrueDisjunction  = makeGroup "truedisjunction"
groupNotFalse         = makeGroup "group-notfalse"

makeGroup :: String -> Id
makeGroup s = describe "Group of logic rules" (propositionalId # s)

-----------------------------------------------------------------------------
-- Inverse of a rule

makeInvRule :: IsId n => (a -> a -> Bool) -> n -> Rule a -> Rule (Context a)
makeInvRule sim name r =
   addRecognizerBool eqCtx $ setSiblings $ setBuggy (isBuggy r) $ makeRule name (const Nothing)
 where
   eqCtx ca cb = fromMaybe False $ eq <$> fromContext ca <*> fromContext cb
   eq a b = any (sim a) (applyAll r b)
   setSiblings n = foldr siblingOf n (ruleSiblings r) -- to do: use siblingsOf

makeInvRuleWithUse :: (IsTerm a, IsTerm b, IsId n, Show a)
                => (Context a -> Context a -> Bool) -> n -> Rule b -> Rule (Context a)
makeInvRuleWithUse sim name r =
   addRecognizerBool eq $ setSiblings $ setBuggy (isBuggy r) $ makeRule name (const Nothing)
 where
   eq a b = any (sim a) (applyAll (somewhere (use r)) b)
   setSiblings n = foldr siblingOf n (ruleSiblings r)

collect :: View a (a, a) -> Isomorphism a [a]
collect v = f <-> g
 where
   f x = maybe [x] (\(y, z) -> f y ++ f z) (match v x)
   g   = foldr1 (curry (build v))

andView, orView, eqView :: View (Logic a) (Logic a, Logic a)
andView = makeView isAnd (uncurry (<&&>))
orView  = makeView isOr  (uncurry (<||>))
eqView  = makeView isEq  (uncurry equivalent)
 where
   isEq (p :<->: q) = Just (p, q)
   isEq _           = Nothing

-- A specialized variant of the somewhere traversal combinator. Apply
-- the strategy only at (top-level) disjuncts
somewhereOr :: IsStrategy g => g (Context SLogic) -> Strategy (Context SLogic)
somewhereOr = somewhereWhen $ \a -> 
   case currentInContext a of
      Just (_ :||: _) -> False
      _               -> True

somewhereAnd :: IsStrategy g => g (Context SLogic) -> Strategy (Context SLogic)
somewhereAnd = somewhereWhen $ \a -> 
   case currentInContext a of
      Just (_ :&&: _) -> False
      _               -> True

infix 6 ===, ==>, <=>

(===), (==>), (<=>) :: Eq a => Logic a -> Logic a -> Bool
(===)   = eqLogic
p ==> q = tautology (p :->: q)
p <=> q = tautology (p :<->: q)