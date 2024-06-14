module Domain.Logic.Inductive.Constraints where

import Control.Monad
import Data.Either
import Data.Maybe
import qualified Data.Set as S
import Ideas.Common.Library
import Ideas.Utils.Prelude
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.RelProof
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.Theorem
import qualified Domain.Logic.Formula as Logic
import Ideas.Common.Constraint

caseConstraints :: [Constraint Inductive]
caseConstraints = 
   baseStepsFinished : ihStepsFinished : inductiveStepsFinished : concatMap f knownProofSteps
 where
   f ps = [caseIntroduced ps, caseFinished ps]

-- for unrecognized cases, check for 'buggy cases' such as for p && q
-- use presence/absence of ihsteps as an indicator for intention to write base/inductive case
casesRecognized :: Constraint Inductive
casesRecognized = makeConstraint "cases-recognized" $ \ind ->
   case [ (nr, (mps, rp)) | (nr, (mps, rp)) <- zip [0 :: Int ..] (proofs ind), isInvalid mps ] of
      []   -> return ()
      (nr, (mps, rp)):_ ->
         case matchLhs (theorem (initial ind)) (topExpr rp) of 
            Just (sub, _) 
               | buggySub sub -> 
                    if userBaseStep mps
                    then violation $ show nr ++ ": invalid composed base case"
                    else violation $ show nr ++ ": invalid atoms in inductive case" 
               | otherwise ->
                    return ()
            Nothing -> 
               violation $ show nr ++ ": case not recognized"
 where
    isInvalid Nothing = True
    isInvalid (Just (UserStep _ Nothing)) = True
    isInvalid _ = False

    userBaseStep (Just (UserStep "basestep" _)) = True
    userBaseStep _ = False

    buggySub :: Substitution -> Bool
    buggySub [(_, TCon sym args)] 
       | sym `elem` [Logic.andSymbol, Logic.orSymbol, Logic.impliesSymbol, Logic.notSymbol] 
         && all isAtom args = True
    buggySub _ = False

    isAtom :: Term -> Bool
    isAtom (TVar s) = s `elem` knownAtoms
    isAtom _ = False

caseIntroduced :: ProofStep -> Constraint Inductive
caseIntroduced ps = makeConstraint ("case-introduced" # ps) $ \ind -> do
   unless (ps `elem` map fromElement (language (initial ind))) Irrelevant
   unless (Just ps `elem` map fst (proofs ind)) $ violation ""

caseFinished :: ProofStep -> Constraint Inductive
caseFinished ps = makeConstraint ("case-finished" # ps) $ \ind -> do
   rp <- relevance $ lookupM (Just ps) (proofs ind)
   unless (isNothing (isOpen rp)) $ violation ""

baseStepsFinished :: Constraint Inductive
baseStepsFinished = makeConstraint "basesteps-finished" $ \ind -> do
   let specials = specialAtoms (language (initial ind))
       isAtomVar (Just (BaseStep s)) = s `elem` knownAtoms && s `notElem` specials
       isAtomVar _ = False

   rps <- relevance $ forM specials $ \a ->
             lookupM (Just (BaseStep a)) (proofs ind)
   rp  <- case filter (isAtomVar . fst) (proofs ind) of
             [(_, rp)] -> return rp
             _         -> violation "no atom var" --komt deze hier?
   unless (all (isNothing . isOpen) (rp:rps)) $ violation ""

ihStepsFinished :: Constraint Inductive
ihStepsFinished = makeConstraint "ihsteps-finished" $ \ind -> do
   let ps = metavarProofs ind
   unless (length ps == 2) Irrelevant
   unless (all (isNothing . isOpen . snd) ps) $ violation ""

inductiveStepsFinished :: Constraint Inductive
inductiveStepsFinished = makeConstraint "inductivesteps-finished" $ \ind -> do
   let cases = rights (language (initial ind))
   rps <- relevance $ forM cases $ \c -> 
             lookupM (Just (InductiveStep c)) (proofs ind)
   unless (all (isNothing . isOpen) rps) $ violation ""

lookupM :: (Show a, Eq a) => a -> [(a, b)] -> Result b
lookupM a xs = maybe (violation $ "not found: " ++ show a) return (lookup a xs)

checkMetaVars :: Constraint Inductive
checkMetaVars = makeConstraint "check-metavars" $ \ind -> do
   unless (keepsMetaVars (theorem (initial ind))) Irrelevant
   let ps = filter (isInductiveStep . fst . snd) (f ind)  --todo: gebruik inductiveStepProofs uit data
   forM_ ps $ \(i, (_, rp)) -> 
      getResult (checkLostMetaVarsInProof i) rp <%> getResult (checkMetaVarsInProof i) rp
 where
   isInductiveStep (Just (InductiveStep _)) = True
   isInductiveStep _ = False

   f ind =  [ (show i, prf) | (i, prf) <- zip [0 :: Int ..] (proofs ind)]
       
(<%>) :: Result () -> Result () -> Result ()
Violation s <%> _ = Violation s
_ <%> Violation s = Violation s
Ok _ <%> Ok _     = Ok ()
_ <%> _           = Irrelevant

checkMetaVarsInProof :: String -> Constraint RelProof
checkMetaVarsInProof loc = makeConstraint "check-metavars-proof" $ \rp ->
   let sets = map getMetaVars (allExprs rp)
   in if allsame sets then return () else violation $ "different metavars: " ++ loc   
   
checkLostMetaVarsInProof :: String -> Constraint RelProof
checkLostMetaVarsInProof loc = makeConstraint "check-lostmetavars-proof" $ \rp ->
   let sets = map getMetaVars (allExprs rp)
   in when (any null sets) $ violation $ "lost metavars: "++ loc

checkUsedMetaVars :: Constraint Inductive
checkUsedMetaVars = makeConstraint "check-used-metavars" $ \ind -> do
   let introduced = map fst (metavarProofs ind)
   forM_ (inductiveStepProofs ind) $ \(i, (_, rp)) -> do
      let loc = show i
      when (null introduced) $       violation ("no induction hypotheses: " ++ loc )  -- deze is nu overbodig geworden?
      forM_ (zip [0 :: Int ..] (allExprs rp)) $ \(nr, e) -> do         
         let mvs = getMetaVars e
         forM_ (S.toList mvs) $ \mv -> 
            unless (mv `elem` introduced) $ 
               violation $ loc ++ " linenr ." ++ show nr ++ ":" ++ mv ++ " not in induction hypothesis"

checkNumberHypotheses :: Constraint Inductive --overbodig? je komt hier niet zodra je aan de inductieve gevallen begint
checkNumberHypotheses = makeConstraint "check-number-hypotheses" $ \ind -> do
   let numberhyp = length (metavarProofs ind)
   forM_ (inductiveStepProofs ind) $ \(i, (theCase, _)) -> do
      let loc = show i
      unless (numberhyp > 0) $       violation ("no induction hypotheses: " ++ loc )  
      unless (connarity (fromJust theCase) <= numberhyp) $ 
               violation $ loc ++ ":" ++ show  theCase ++ " needs " ++ show  (connarity (fromJust theCase)) ++  " inductionhypotheses"

checkPlaceHypotheses :: Constraint Inductive --overbodig in huidige versie, volgorde ligt in frontend vast
checkPlaceHypotheses = makeConstraint "check-place-hypotheses" $ \ind -> do
   unless (not (null (ihStepProofs ind)) && not (null (inductiveStepProofs ind))) Irrelevant
   let indicesIh = map fst (ihStepProofs ind) 
       indicesInductiveSteps = map fst (inductiveStepProofs ind)
   unless (maximum indicesIh < minimum indicesInductiveSteps) $ 
      violation "inductionhypotheses introduced after inductive case" 