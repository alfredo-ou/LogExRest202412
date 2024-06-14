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
-----------------------------------------------------------------------------

module Domain.Logic.Strategies
   ( dnfStrategy, cnfStrategy
   , orRules, andRules, nnfStep, simplifyStep
   , deMorgan, deMorganOr, deMorganAnd, distrAnd, distrOr
   , eliminateImplEquiv
   , specialDeMorganNot, specialDistrNot, specialGroupLiterals
   , groupLiteralsOr, groupLiteralsAnd
   ) where

import Control.Monad
import Data.List
import Data.Maybe
import Domain.Logic.Formula
import Domain.Logic.GeneralizedRules
import Domain.Logic.Generator
import Domain.Logic.Rules
import Domain.Logic.Utils
import Ideas.Common.Library
import Ideas.Common.Strategy.Legacy
import Ideas.Common.Traversal.Navigator
import Prelude hiding ((<*>))

-----------------------------------------------------------------------------
-- Normal forms

dnfStrategy :: LabeledStrategy (Context SLogic)
dnfStrategy = normalized $ label "DNF" $ repeatS $
   orRules <|> somewhereOr (nnfStep |> distrAnd)

cnfStrategy :: LabeledStrategy (Context SLogic)
cnfStrategy = normalized $ label "CNF" $ repeatS $
   andRules <|> somewhereAnd (nnfStep |> distrOr)

-- normalize the propositions (by making and/or right associative)
normalized :: LabeledStrategy (Context SLogic) -> LabeledStrategy (Context SLogic)
normalized = cleanUpStrategy f
 where
   f :: Context SLogic -> Context SLogic
   f ctx = fromMaybe ctx $
      navigateTo (location ctx) (changeInContext normalizeLogicA (top ctx))

-----------------------------------------------------------------
-- Sub-strategies

orRules :: LabeledStrategy (Context SLogic)
orRules = label "OrRules" $ useRules
   [ruleFalseOr, ruleTrueOr, ruleIdempOr, ruleAbsorpOr, ruleComplOr, absorptionOrSubsetCom, absorptionOrSubsetSort]


andRules :: LabeledStrategy (Context SLogic)
andRules = label "AndRules" $ useRules
   [ruleFalseAnd, ruleTrueAnd, ruleIdempAnd, ruleAbsorpAnd, ruleComplAnd, absorptionAndSubsetCom, absorptionAndSubsetSort]

-- A step towards Negation Normal Form (NNF)
nnfStep :: Strategy (Context SLogic)
nnfStep =
      simplifyStep
   |> (remove specialGroupLiterals >|> specialDistrNot >|> specialDeMorganNot)
   |> (eliminateImplEquiv >|> deMorgan)

simplifyStep :: LabeledStrategy (Context SLogic)
simplifyStep = label "Simplify" $ oncetdPref $
   orRules <|> andRules <|>
   useRules [ruleNotTrue, ruleNotFalse, ruleDoubleNeg]

deMorganOr :: Strategy (Context SLogic)
deMorganOr = liftToContext generalRuleDeMorganOr >|> liftToContext ruleDeMorganOr

deMorganAnd :: Strategy (Context SLogic)
deMorganAnd = liftToContext generalRuleDeMorganAnd >|> liftToContext ruleDeMorganAnd

deMorgan :: LabeledStrategy (Context SLogic)
deMorgan = label "DeMorgan" $ oncetdPref $
   deMorganOr <|> deMorganAnd

distrAnd :: LabeledStrategy (Context SLogic)
distrAnd = label "DistrAnd" $ oncebuPref $
   liftToContext generalRuleDistrAnd >|> liftToContext ruleDistrAnd

distrOr :: LabeledStrategy (Context SLogic)
distrOr = label "DistrOr" $ oncebuPref $
   liftToContext generalRuleDistrOr >|> liftToContext ruleDistrOr

eliminateImplEquiv :: LabeledStrategy (Context SLogic)
eliminateImplEquiv = label "EliminateImplEquiv" $
   somewhere (liftToContext ruleDefImpl)
   >|>
   oncebuPref (liftToContext ruleDefEquiv)

-- specialization of De Morgan rules with a not inside (gives higher priority)
specialDeMorganNot :: LabeledStrategy (Context SLogic)
specialDeMorganNot = label "SpecialDeMorganNot" $ somewhere $
   (check (cond disjunctions) <*> deMorganOr) <|>
   (check (cond conjunctions) <*> deMorganAnd)
 where
   cond f ctx = case currentInContext ctx of
                   Just (Not x) ->
                      let ys = f x in length ys > 1 && any notComposed ys
                   _ -> False
   notComposed (Not (Var _)) = False
   notComposed (Not _)       = True
   notComposed _             = False


specialDistrNot :: LabeledStrategy (Context SLogic)
specialDistrNot = label "SpecialDistrNot" $ somewhere $ liftToContext $
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

specialGroupLiterals :: LabeledStrategy (Context SLogic)
specialGroupLiterals = label "SpecialSort" $ somewhere $
   liftToContext groupLiteralsOr <|> liftToContext groupLiteralsAnd

-- p \/ q \/ ~p  ~> reorder p and ~p
-- p \/ q \/ p   ~> reorder p's
groupLiteralsOr :: Rule SLogic
groupLiteralsOr = siblingOf groupCommutativity $ ruleMaybe "logic.propositional.ComplOr.sort" $ \p -> do
   let xs = disjunctions p
       ys = sortLiterals xs
   guard (xs /= ys)
   return (ors ys)

-- p /\ q /\ ~p  ~> reorder p and ~p
-- p /\ q /\ p   ~> reorder p's
groupLiteralsAnd :: Rule SLogic
groupLiteralsAnd = siblingOf groupCommutativity $ ruleMaybe "logic.propositional.ComplAnd.sort" $ \p -> do
   let xs = conjunctions p
       ys = sortLiterals xs
   guard (xs /= ys)
   return (ands ys)

sortLiterals :: [SLogic] -> [SLogic]
sortLiterals [] = []
sortLiterals (p:ps) = p : ys ++ sortLiterals zs
 where
   (ys, zs) = partition (\x -> x == p || x `isNegated` p) ps
   isNegated (Not x) y = y `elem` [x, Not (Not x)]
   isNegated x y       = y == Not x

-- local helper function
useRules :: [Rule SLogic] -> Strategy (Context SLogic)
useRules = alternatives . map liftToContext