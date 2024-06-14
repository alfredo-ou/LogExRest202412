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
-- Exercise for the logic domain, used for the OUNL course
-- "Discrete Wiskunde A (DWA)"
--
-----------------------------------------------------------------------------

module Domain.Logic.NormalForms.Exercises
   ( dnfExercise, dnfUnicodeExercise, cnfExercise, cnfUnicodeExercise
   , extraLogicRules
   ) where

import Data.Maybe
import Domain.Logic.BuggyRules
import Domain.Logic.Examples
import Domain.Logic.Formula
import Domain.Logic.GeneralizedRules
import Domain.Logic.Generator
import Domain.Logic.InverseRules
import Domain.Logic.Parser
import Domain.Logic.Rules
import Domain.Logic.Strategies
import Domain.Logic.Utils
import Ideas.Common.Library 
import Ideas.Common.Examples
import Test.QuickCheck
import Ideas.Utils.Uniplate
import Ideas.Utils.Prelude (ShowString(..))

-- Currently, we use the DWA strategy
dnfExercise :: Exercise SLogic
dnfExercise = makeExercise
   { exerciseId    = describe "Proposition to DNF" $
                        propositionalId # "dnf"
   , status        = Stable
   , parser        = parseLogicPars
   , prettyPrinter = ppLogic
   , equivalence   = withoutContext eqLogic
   , similarity    = withoutContext equalLogicA
   , ready         = predicate isDNF
   , suitable      = predicate notTooManyEquivs
   , extraRules    = generalAssoc : generalComm : map liftToContext extraLogicRules ++ buggyRules
   , strategy      = dnfStrategy
   , navigation    = navigator
   , examples      = dnfExamples <> makeRandomGenerator dnfExerciseGenerator
        {- 
        -- temporary, for Josjes demo only
        examplesWithDifficulty [ (dif, Not F :&&: (T :->: Var (ShowString "r")))  
                               | dif <- [Easy .. Difficult] 
                               ] -}
   }

-- Direct support for unicode characters
dnfUnicodeExercise :: Exercise SLogic
dnfUnicodeExercise = dnfExercise
   { exerciseId    = describe "Proposition to DNF (unicode support)" $
                        propositionalId # "dnf.unicode"
   , parser        = parseLogicUnicodePars
   , prettyPrinter = ppLogicUnicode
   }

cnfExercise :: Exercise SLogic
cnfExercise = dnfExercise
   { exerciseId     = describe "Proposition to CNF" $
                         propositionalId # "cnf"
   , ready          = predicate isCNF
   , strategy       = cnfStrategy
   , examples       = cnfExamples <> 
                      makeRandomGenerator cnfExerciseGenerator -- <>
                      -- forTesting (random (arbitrary `suchThat` notTooManyEquivs))
   }

cnfUnicodeExercise :: Exercise SLogic
cnfUnicodeExercise = cnfExercise
   { exerciseId     = describe "Proposition to CNF (unicode support)" $
                         propositionalId # "cnf.unicode"
   , parser         = parseLogicUnicodePars
   , prettyPrinter  = ppLogicUnicode
   }

extraLogicRules :: [Rule SLogic]
extraLogicRules =
   [ ruleCommOr, ruleCommAnd
    -- , ruleAssocOr, ruleAssocAnd
   , generalRuleDistrOr, ruleDistrOr
   , generalRuleDistrAnd, ruleDistrAnd
   , inverseDeMorganOr, inverseDeMorganAnd
   , inverseAndOverOr, inverseOrOverAnd
   , inverseIdempOr, inverseIdempAnd
   , generalRuleInvDoubleNegAnd, generalRuleInvDoubleNegOr
   ] ++ inverseRules

makeRandomGenerator :: (Maybe Difficulty -> Gen a) -> Examples a
makeRandomGenerator f = mconcat (map mk [Easy, Medium, Difficult])
 where
   mk d = difficulty d (random (f (Just d)))

notTooManyEquivs :: SLogic -> Bool
notTooManyEquivs = (<=2) . countEquivalences

dnfExerciseGenerator :: Maybe Difficulty -> Gen SLogic
dnfExerciseGenerator = exerciseGeneratorFor dnfExercise

cnfExerciseGenerator :: Maybe Difficulty -> Gen SLogic
cnfExerciseGenerator = exerciseGeneratorFor cnfUnicodeExercise

exerciseGeneratorFor :: Exercise SLogic -> Maybe Difficulty -> Gen SLogic
exerciseGeneratorFor ex mdif = 
   let (gen, (minStep, maxStep)) = generateLevel (fromMaybe Medium mdif)
       ok p = let i = fromMaybe maxBound (stepsRemaining maxStep p)
              in notTooManyEquivs p && i >= minStep && i <= maxStep && (checkLength2 ex p <= 30)
   in gen `suchThat` ok
 where 
   stepsRemaining i =
      checkLength i ex

checkLength :: Int -> Exercise a -> a -> Maybe Int
checkLength n ex a = defaultDerivation ex a >>= rec 0 . steps
 where
   rec i []       =  Just i
   rec i (_:xs)
      | i >= n    = Nothing
      | otherwise = rec (i+1) xs

checkLength2 :: Exercise SLogic -> SLogic -> Int
checkLength2 ex a = maximum $ map (formulaLength . fromJust . fromContext) (terms (fromJust (defaultDerivation ex a))) 
 
formulaLength :: Logic a -> Int
formulaLength p = 1 + sum (map formulaLength (children p))

seeprf n = printDerivation dnfExercise (snd (topLevelExamples dnfExamples !! n))   

testderivation:: Exercise SLogic -> SLogic -> [Context SLogic]
testderivation ex a =  terms (fromJust (defaultDerivation ex a))

{-
seeLength n a = checkLength n testExercise a  

testExercise :: Exercise SLogic
testExercise = makeExercise
   { exerciseId     = describe "Proposition to DNF" $
                         propositionalId # "dnf"
   , status         = Stable
   , parser         = parseLogicPars
   , prettyPrinter  = ppLogic
   , equivalence    = withoutContext eqLogic
   , similarity     = withoutContext equalLogicA
   , ready          = predicate isDNF
   , suitable       = predicate notTooManyEquivs
   , extraRules     = map liftToContext (extraLogicRules ++ buggyRules)
   , strategy       = buggyS
   , navigation     = navigator
   , examples       = dnfExamples <> 
                      makeRandomGenerator dnfExerciseGenerator -- <> 
                   --   forTesting (random (arbitrary `suchThat` notTooManyEquivs))
   }                
   

test  = x /= y && equalLogicAC x y && not (equalLogicA x y)   -- equalLogicAC (p :||: q :||: r :||: s) (p :||: q :||: r :||: s)
          where  
            x = (r :||: q :||: (p :||: s))
            y = ((p :||: q) :||: r :||: s)
            (p, q, r, s) = (Var "p", Var "q", Var "r", Var "s")

  

testCase ::  IO ()
testCase = do
   let txt = printDerivation (useRules  buggyRules) (Var (ShowString "p") :&&: Var(ShowString "q") :&&: Var(ShowString "r"))
   writeFile "out.txt" txt
   putStrLn txt   

testCase ::  IO ()
testCase = do
   let txt = printDerivation  dnfStrategy (dnfExamples !! 0)-- (useRules  buggyRules) (Var (ShowString "p") :&&: Var(ShowString "q") :&&: Var(ShowString "r"))
  -- writeFile "out.txt" txt
 --  putStrLn txt   


-- QuickCheck property to monitor the number of steps needed
-- to normalize a random proposition (30-40% is ok)

testGen :: Property
testGen = forAll generateLogic $ \p ->
   let n = steps p
   in countEquivalences p <= 2 ==> label (show (n >= 4 && n <= 12)) True

testme :: IO ()
testme = quickCheck testGen

start = ((r :<->: p) :||: (q :->: s)) :&&: (Not s :<->: (p :||: r))
 where
  (p, q, r, s) = (Var "p", Var "q", Var "r", Var "s")

go = derivation . emptyState dnfExercise
-}