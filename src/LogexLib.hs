module LogexLib (ideasLib) where

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
-- Main module for feedback services
--
-----------------------------------------------------------------------------
--module Main (main, ideasLogic) where

import Control.Arrow
import Ideas.Common.Constraint
import Ideas.Common.Context
import Ideas.Common.Library
import Ideas.Utils.Prelude (Some(..))
import Ideas.Service.BasicServices
import Ideas.Service.Diagnose
import Ideas.Service.Types
import Ideas.Service.State
import Ideas.Main.Default
import Domain.Logic.NormalForms.Exercises
import Domain.Logic.Consequence.Exercise
import Domain.Logic.Equivalence.Exercise
import qualified Domain.Logic.Equivalence.ExerciseRP as New
import Domain.Logic.Axiomatic.Exercise
import Domain.Logic.Inductive.Exercise

ideasLogic :: DomainReasoner
ideasLogic = describe "Domain reasoner for logic" $
   (newDomainReasoner "ideas-logic")
      { exercises = myExercises
      , services  = myServices
      , aliases   = myAliases
      , scripts   = myScripts
      }

myExercises :: [Some Exercise]
myExercises =
   [ Some dnfExercise
   , Some dnfUnicodeExercise
   , Some cnfExercise
   , Some cnfUnicodeExercise
   , Some proofExercise
   , Some New.proofExercise
   , Some New.proofUnicodeExercise
   , Some proofUnicodeExercise
   , Some proofTopExercise
   , Some consequenceExercise
   , Some logaxExercise
   , Some inductiveExercise
   , Some inductiveGuidedExercise
   ]

myServices :: [Service]
myServices = metaServiceList ideasLogic ++
   diagnoseS : mySolution : myDerivationS : myOneFinal : myExampleFinal : constraintsS : filter p serviceList
 where
   p = (`notElem` [newId "basic.solution", newId "basic.derivation", newId "basic.onefinal", newId "basic.diagnose"]) . getId

-- ServiceList
mySolution :: Service
mySolution = makeService "basic.solution"
   "Returns one possible worked-out solution starting with the \
   \current expression. The first optional argument lets you configure the \
   \strategy, i.e., make some minor modifications to it. Rules used and \
   \intermediate expressions are returned in a list. (Extended service with 100 steps)" $
   solutionMaxSteps 100 ::: tMaybe tStrategyCfg .-> tState .-> tError (tDerivation tStepInfo tContext)

myDerivationS :: Service
myDerivationS = deprecate $ makeService "basic.derivation"
   "See 'solution' service." $
   serviceFunction mySolution

myOneFinal :: Service
myOneFinal = makeService "basic.onefinal"
   "Returns a final term, after taking zero or more steps, by applying the \
   \strategy. (Extended service with 100 steps)" $
   fmap lastTerm . solutionMaxSteps 100 Nothing ::: tState .-> tError tContext

myExampleFinal :: Service
myExampleFinal = makeService "basic.example-final"
   "Returns a final term, after taking zero or more steps, by applying the \
   \strategy to an example. (Extended service with 100 steps)" $
   f ::: tQCGen .-> tExercise .-> tInt .-> tMaybe tUserId .-> tError tContext
 where
   f rng ex nr userId =
      case drop nr (examplesAsList ex) of
         []  -> Left "No such example"
         a:_ -> fmap lastTerm $ solutionMaxSteps 100 Nothing $ startState rng ex userId a

constraintsS :: Service
constraintsS = makeService "basic.constraints"
   "Check all constraints" $
   checkConstraints ::: tState .-> tList (tTuple3 tConstraint (Tag "value" tString) (tMaybe (Tag "message" tString)))

checkConstraints :: State a -> [(Constraint (Ideas.Common.Library.Context a), String, Maybe String)]
checkConstraints st = map f (constraints (exercise st))
 where
   f c = let (val, msg) = g (getResult c (stateContext st))
         in (c, val, msg)

   g (Ok _)          = ("ok", Nothing)
   g Irrelevant      = ("irrelevant", Nothing)
   g (Violation msg) = ("error", Just msg) -- to do: rename (but this requires updating front-ends)

myAliases :: [(Id, Id)]
myAliases = map (newId *** newId)
   [ ("logic.dnf",                "logic.propositional.dnf")
   , ("logic.dnf-unicode",        "logic.propositional.dnf.unicode")
   , ("logic.proof",              "logic.propositional.proof")
   ]

myScripts :: [(Id, FilePath)]
myScripts =
   [ (getId dnfExercise,         "logic.txt")
   , (getId dnfUnicodeExercise,  "logic.txt")
   ]

------------------------------------------------------------------------------
-- Extended diagnose service with constraints

diagnoseS :: Service
diagnoseS = makeService "basic.diagnose"
   "Diagnose an expression submitted by a student. Possible diagnosis are \
   \Buggy (a common misconception was detected), NotEquivalent (something is \
   \wrong, but we don't know what), Similar (the expression is pretty similar \
   \to the last expression in the derivation), Expected (the submitted \
   \expression was anticipated by the strategy), Detour (the submitted \
   \expression was not expected by the strategy, but the applied rule was \
   \detected), and Correct (it is correct, but we don't know which rule was \
   \applied). Extended version for logic domain: check predicates for NotEquiv." $
   diagnoseWithPredicates ::: tState .-> tContext .-> tMaybe tId .-> tDiagnosis

--------------------------------------------------------------------------------

diagnoseWithPredicates :: State a -> Ideas.Common.Library.Context a -> Maybe Id -> Diagnosis a
diagnoseWithPredicates st ctx mid = f (diagnoseOption True st ctx mid)
 where
   f (NotEquivalent "") =
      case filter keep (violations (exercise st) ctx) of
         (x, msg):_ -> NotEquivalent $ show x ++ if null msg then "" else ": " ++ msg
         [] | not (any keep (violations (exercise st) (stateContext st))) ->
                 NotEquivalent []
            | otherwise -> -- special case: previous state is invalid (constraint violated)
                 Correct (finished st) st
   f d = d

   -- quick fix: some constraints only have to hold at the end (to be 'ready')
   keep (x, _) = qualifiers x /= ["case-introduced"]

--main :: IO ()
--main = defaultMain ideasLogic

ideasLib :: IO ()
ideasLib = do
        putStrLn "LogexLib"