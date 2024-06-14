module Domain.Logic.Inductive.Exercise
   ( inductiveExercise, inductiveGuidedExercise
   ) where

import Data.List 
import Data.Maybe
import Data.Either
import Domain.Logic.Inductive.Constraints
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.Examples
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.RelProof
import Domain.Logic.Inductive.Strategies
import Domain.Logic.Inductive.Theorem 
import Domain.Math.Expr hiding ((.*.), (./.))
import Ideas.Common.Library
import Ideas.Encoding.Encoder
import Ideas.Common.Constraint
import Control.Monad
import qualified Domain.Logic.Formula as OM

--- debugging functions
_go :: IO ()
_go = do
   let txt = showDerivation inductiveExercise (head $ examplesAsList inductiveExercise)
   writeFile "out.txt" txt
   putStrLn txt
     
_gog :: IO ()
_gog = do
   let txt = showDerivation inductiveGuidedExercise (head $ examplesAsList inductiveGuidedExercise)
   writeFile "out.txt" txt
   putStrLn txt  
   
_goN :: Int -> IO ()
_goN n = do
   let txt = showDerivation inductiveGuidedExercise (examplesAsList inductiveGuidedExercise !! n)
   writeFile "out.txt" txt
   putStrLn txt
   
_seeN :: Int -> IO ()
_seeN n = do
   let txt = showDerivation inductiveExercise (examplesAsList inductiveExercise !! n)
   writeFile "out.txt" txt
   putStrLn txt       

-----------------------------------------------------------------------------------------------------

{-
allObjects :: [Inductive]
allObjects = 
   [ obj
   | p      <- examplesAsList inductiveExercise
   , der    <- maybeToList (defaultDerivation inductiveExercise p)
   , ctxobj <- terms der
   , obj    <- maybeToList (fromContext ctxobj)
   ]

testAll :: IO ()
testAll = mapM_ testObject allObjects

testObject :: Inductive -> IO ()
testObject p
   | Just p == q = putStr "."
   | isJust q    = fail $ "\n" ++ show p ++ "\n\n === vs. \n\n" ++ show (fromJust q)
   | otherwise   = fail $ "\n" ++ show p ++ "\n\n === vs. \n\n" ++ show q
 where
   q = fromJSON (toJSON p)

this = fromJust $ fromContext $ lastTerm $ fromJust $ defaultDerivation inductiveExercise (makeInductive (head cases))
help = toJSON this
back = fromJSON help :: Maybe Inductive 
-}
   
inductiveExercise :: Exercise Inductive
inductiveExercise = jsonEncoding $ emptyExercise
   { exerciseId    = describe "Inductive proofs" $ newId "logic.propositional.inductive"
   , status        = Experimental
   , prettyPrinter = show
   , equivalence   = withoutContext eqInductive
   , similarity    = withoutContext similarInductive
   , navigation    = termNavigator
   , hasTermView   = Just termView
   , ruleOrdering  = ruleOrderingWith $ [closeEqualProof, closeSameProof, closeLessProof] ++ definitionCloseRules ++ exprCloseRules
   , strategy      = label "inductive" $ liftToContext inductiveStrategy
   , constraints   = map liftToContext [checkNumberHypotheses, checkMetaVars, checkUsedMetaVars, checkPlaceHypotheses,
                         checkInductive, casesRecognized, checkProofSteps]
   , ready         = predicate inductiveReady
   , examples      = examplesWithDifficulty [ (Medium, makeInductive ini) | ini <- cases ]
   }

inductiveGuidedExercise :: Exercise Inductive
inductiveGuidedExercise = inductiveExercise
   { exerciseId  = describe "Inductive proofs" $ newId "logic.propositional.inductive-guided"
   , strategy    = label "inductive" $ liftToContext inductiveGuidedStrategy
   , equivalence = withoutContext eqGuidedInductive
   , constraints = map liftToContext $ checkMetaVars : checkUsedMetaVars :
                         checkInductive : casesRecognized : checkProofStepsGuided : checkProofSteps : caseConstraints
   }   
   
inductiveReady :: Inductive -> Bool
inductiveReady a = 
   all (readyRelProof th . snd) cs &&                -- alle bewijzen zijn af
   all (isJust . fst) cs   &&                        -- alle gevallen zijn herkend
   concatMap isCase elts ~= rights lan &&            -- alle cases zitten erin
   specials ~= lefts lan &&                          -- alle speciale variabelen zitten erin
   length (concatMap isIH elts) == 2 &&              -- er zijn precies twee inductie metavariabelen
   length base == 1                                  -- er is precies 1 basisvariabele
 where
   cs   = proofs a
   th   = theorem (initial a)
   lan  = language (initial a)
   elts = mapMaybe fst cs
   (specials, base) = partition (`elem` lefts lan) (concatMap isBase elts)

   xs ~= ys = sort xs == sort ys

   isCase (InductiveStep c) = [c]
   isCase _ = []

   isBase (BaseStep s) = [s]
   isBase _ = []

   isIH (IHStep s) = [s]
   isIH _ = [] 

-- For equivalence, only check constraints (and that initials have not been changed)
eqGuidedInductive :: Inductive -> Inductive -> Bool
eqGuidedInductive inx iny =
   checkInstances inx && checkInstances iny &&
   checkProofStepsBool inx && checkProofStepsBool iny &&
   isNothing (isViolated casesRecognized inx) &&
   isNothing (isViolated casesRecognized iny) &&
   isNothing (isViolated checkUsedMetaVars inx) &&
   isNothing (isViolated checkUsedMetaVars iny) &&
   initial inx == initial iny && 
   and [ isJust key && checkRelProof th x
       | (key, x) <- proofs inx ++ proofs iny
       ]
 where
   th = theorem (initial inx)
   
-- For equivalence, only check constraints (and that initials have not been changed)
eqInductive :: Inductive -> Inductive -> Bool
eqInductive inx iny =
   checkInstances inx && checkInstances iny &&
   checkProofStepsBool inx && checkProofStepsBool iny &&
   isNothing (isViolated checkUsedMetaVars inx) &&
   isNothing (isViolated checkUsedMetaVars iny) &&
   isNothing (isViolated checkPlaceHypotheses inx) &&
   isNothing (isViolated checkPlaceHypotheses iny) &&
   
   initial inx == initial iny && 
   isNothing (isViolated checkProofSteps inx) && 
   isNothing (isViolated checkProofSteps iny) && and
      [ isJust key && checkRelProof th x
      | (key, x) <- proofs inx ++ proofs iny
      ]
 where
   th = theorem (initial inx)

findDoubleCase :: Inductive -> Maybe ProofStep
findDoubleCase = rec . mapMaybe fst . proofs
 where
   rec []     = Nothing
   rec (x:xs)
      | x `elem` xs = Just x
      | otherwise   = rec xs

checkInductive :: Constraint Inductive
checkInductive = makeConstraint "check-inductive" $ \inx -> andResults $
   [ getResult (checkIHRelProof' (theorem (initial inx)) i) rp | (i, (_, rp)) <- f inx ] ++
   [getResult (subConstraints f "check-instance" (checkInstance (initial inx))) inx]  ++
   map (getResult (checkInstance (initial inx))) (proofs inx) ++
   [ getResult (checkRelProof' (theorem (initial inx)) (maybe "" show mps)) rp | (mps, rp) <- proofs inx]
  where
    f inx = [ (show i, prf) | (i, prf) <- zip [0 :: Int ..] (proofs inx) ]
 
-- to do: move functions to ideas library
andResults :: [Result ()] -> Result ()
andResults [] = Ok ()
andResults xs = foldr1 (<&>) xs

(<&>) :: Result () -> Result () -> Result ()
Violation s <&> _ = Violation s
_ <&> Violation s = Violation s
Ok _ <&> Ok _ = Ok ()
_ <&> _       = Irrelevant

checkInstances :: Inductive -> Bool
checkInstances inx = all (isNothing . isViolated (checkInstance (initial inx))) (proofs inx)

checkInstance :: Initial -> Constraint (Maybe ProofStep, RelProof)
checkInstance inx = makeConstraint "check-instance" $ \(st, rp) -> do
   let lan = language inx
   
   case st of
      Just (BaseStep _) -> do
         case matchLhs (theorem inx) (topExpr rp) of
              Just _  -> return ()
              Nothing -> violation "invalid instantiation for top expr" 
         case matchRhs (theorem inx) (bottomExpr rp) of
             Just _  -> return ()
             Nothing -> violation "invalid instantiation for bottom expr"
         case matchTheorem (theorem inx) (topExpr rp) (bottomExpr rp) of
            Just _  -> return ()       
            Nothing -> violation $ show st ++ "not an instantiation" -- because case BaseStep was recognized, the mistake will probably in the bottom part, also happens with a different substitution for lhs and rhs, dubbelop met checkRelProof

      Just (InductiveStep _) -> do 
         case checkNotInLanguage lan (topExpr rp) of 
            Nothing -> return ()
            Just s  -> violation $ "connective not in language: " ++ s
         case checkNotInLanguage lan (bottomExpr rp) of 
            Nothing -> return ()
            Just s  -> violation $ "connective not in language: " ++ s
      Just (IHStep _) -> do       
         case matchLhs (theorem inx) (topExpr rp) of
              Just _  -> return ()
              Nothing -> violation "wrongIHTop" 
         case matchRhs (theorem inx) (bottomExpr rp) of
             Just _  -> return ()
             Nothing -> violation "wrongIHBottom"
      _ -> return ()
      
   case matchLhs (theorem inx) (topExpr rp) of
      Just _  -> return ()
      Nothing -> violation "invalid instantiation for top expr" -- this is already diagnosed by casesrecognized??
   
   case matchRhs (theorem inx) (bottomExpr rp) of
      Just _  -> return ()
      Nothing -> violation "invalid instantiation for bottom expr"
      
checkNotInLanguage :: Language -> Expr -> Maybe String
checkNotInLanguage lan e =
   listToMaybe (map show (filter notOk (collectConnectives e)))
 where
   notOk c = c `notElem` rights lan

collectConnectives :: Expr -> [Case]
collectConnectives = rec . toTerm
 where
   rec (TCon s xs) = f s ++ concatMap rec xs
   rec (TList xs)  = concatMap rec xs
   rec _ = []
   
   f s | s == OM.andSymbol     = [AND]
       | s == OM.orSymbol      = [OR]
       | s == OM.notSymbol     = [NEGATION]
       | s == OM.impliesSymbol = [IMPLIES]
       | otherwise             = []

checkProofStepsBool :: Inductive -> Bool
checkProofStepsBool = isNothing . isViolated checkProofSteps

checkProofSteps :: Constraint Inductive
checkProofSteps = makeConstraint "check-proofsteps" $ \in1 -> do
   let cs   = proofs in1
       lan  = language (initial in1)
       elts = mapMaybe fst cs
       isBase (BaseStep s) = [s]
       isBase _ = []
       (_, base) = partition (`elem` lefts lan) (concatMap isBase elts)

   case findDoubleCase in1 of
      Just ps@(IHStep _) -> violation $ show ps ++ ": double IH"
      Just ps -> violation $ show ps ++ ": double case"
      _ -> return ()
   
   unless (length base <= 1) $ 
      violation  "too many basecases"
   
   forM_ (proofs in1) $ \(ps, _) ->
      case ps of
         Just (BaseStep s) | s `notElem` knownAtoms -> violation $ "invalid basestep for " ++ s
         Just (IHStep v) | v `notElem` knownMetaVars -> violation $ "invalid ihstep for " ++ v 
         Just (InductiveStep c) | c `notElem` rights (language (initial in1)) -> violation $ "connective not in language: " ++ show c
         Just (UserStep us (Just (BaseStep s))) -> violation $ "not " ++ us ++ " but basestep " ++ s
         Just (UserStep us (Just (IHStep v))) -> violation $ "not " ++ us ++ " but ihstep " ++ v
         Just (UserStep us (Just (InductiveStep c))) -> violation $ "not " ++ us ++ " but inductivestep " ++ show c 
         Just (UserStep us Nothing) -> violation $ "not " ++ us ++ " (not recognized)"
         Just _ -> return ()
         Nothing -> violation "case not recognized"

checkProofStepsGuided :: Constraint Inductive --toevoegen in equivalentiecheck? en aparte aanroep naar dubbel case dan weg
checkProofStepsGuided = makeConstraint "check-guided-proofsteps" $ \in1 -> do
  let  isBaseStep (BaseStep _) = True
       isBaseStep _ = False

       isIHStep (IHStep _) = True
       isIHStep _ = False

       ini                 = initial in1
       spcs                = map fromAtom (lefts $ language ini)
       ics                 = map fromCase (rights $ language ini)
       present             = mapMaybe fst (proofs in1)
       presentbcs    = filter isBaseStep present \\ spcs
       oneBaseCase         = length presentbcs == 1
       noMissingSpecial    = null (spcs \\ present) 
       zeroOrTwoIH         = length (filter isIHStep present) `elem` [0, 2]
       noMissingIC         = null (ics \\ present) ||( ics \\ present == ics)
   
  case findDoubleCase in1 of
     Just ps -> violation $ show ps ++ ": double case"
     _ -> return ()

  unless oneBaseCase      $ violation $  if null presentbcs then  "missing basecase"  else "too many basecases"
  unless noMissingSpecial $ violation "missing special cases"
  unless zeroOrTwoIH      $ violation "incorrect ih"
  unless noMissingIC      $ violation "incorrect inductive cases" 

{-
-- This check was in RelProof's checkRelProof, as a special case for closed proofs, 
-- without considering the inferred case. Code moved to Exercise, but first see 
-- if this check can ever occur.
checkMetaVarsInHypothesis :: Constraint Inductive
checkMetaVarsInHypothesis = makeConstraint "check-metavars-ih" $ \in1 -> do
   let th = theorem in1
   forM (proofs in1) $ \(mps, rp) ->
    when (mps == Just IHStep) $ do
      -- special check for hypothesis (one triple, with "ih" as motivation)
      case triples d of
         [(e1, (_, m), e2)] | m == "ih" && keepsMetaVars th -> 
            checkHypothesisVars e1 e2
         _ -> return () -}

similarInductive :: Inductive -> Inductive -> Bool
similarInductive inx iny =
   initial inx == initial iny && length xs == length ys && all p (zip xs ys)
 where
   xs = sortBy cmp (proofs inx)
   ys = sortBy cmp (proofs iny)

   cmp (x, _) (y, _) = compare x y

   p ((ex, x), (ey, y)) = 
      ex == ey && similarRelProof x y

