module Domain.Logic.Axiomatic.Rules 
   ( AxiomaticProof, Subgoals(..)
   , goalId
   -- rules 
   , assumptionR, assumptionCloseR, goalR, goalR1, lemmaR, lemmaCloseR
   , axiomAR, axiomBR, axiomCR, axiomACloseR, axiomBCloseR, axiomCCloseR
   , mpRule
   , dedForwardR, dedBackwardR, dedCloseR, renumberR, removeLineR
     -- misc
   , createGoal, forward, createGoal1
   , nRef, n1Ref, n2Ref, n3Ref
   , phiRef, psiRef, chiRef
   , stRef, st1Ref, st2Ref, st3Ref, asRef, subgoalsRef
   -- tijdelijk, om buggy rules te testen en om meer doelen te testen, en vanuit proofdag etc te testen
   , assumption, deductionBackward, deductionForward, introAxiomB, introLemma
   , axiomA, axiomB,axiomC
   ) where

import Ideas.Utils.Prelude   
import Data.List
import Data.Maybe
import Control.Monad
import Domain.Logic.Formula
import Domain.Logic.Axiomatic.Label 
import Domain.Logic.Axiomatic.Lemma
import Domain.Logic.Axiomatic.LinearProof
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Ideas.Common.Library hiding (label)
import qualified Data.Set as S

type AxiomaticProof = Proof AxiomaticLabel Statement

----------------------------------------------------------------------
-- Axiom identifiers

assumptionCloseId :: Id
assumptionCloseId = describe "Motivates an assumption (as|- phi)." $ 
   assumpId # "close"

lemmaCloseId :: Id
lemmaCloseId = describe "Motivates a lemma (as|- phi)." $ 
   lemmaId # "close"

axiomACloseId, axiomBCloseId, axiomCCloseId  :: Id  
axiomACloseId = describe "Motivates an instance of Axiom A (phi, psi)." $ 
   axiomAId # "close"
axiomBCloseId = describe "Motivates an instance of Axiom B (phi, psi, chi)." $ 
   axiomBId # "close"
axiomCCloseId = describe "Motivates an instance of Axiom C (phi, psi)." $ 
   axiomCId # "close" 

dedForwardId, dedBackwardId, dedCloseId :: Id
dedForwardId = describe "Deduction rule applied to phi, As |- psi." $ 
   dedId # "forward"
dedBackwardId = describe "Deduction rule applied to As |- phi -> psi." $ 
   dedId # "backward" 
dedCloseId = describe "Deduction rule applied to (phi, As |- psi) and (As |- phi -> psi)." $ 
   dedId # "close" 

goalId :: Id
goalId = describe "Introduces at line n a new goal st" $ 
   logax # "goal" 

goalId1 :: Id
goalId1 = describe "Introduces a new goal." $ 
   logax # "goal1"   
   
phiRef, psiRef, chiRef :: Ref SLogic
phiRef = makeRef "phi"
psiRef = makeRef "psi"
chiRef = makeRef "chi"

stRef, st1Ref, st2Ref, st3Ref :: Ref Statement
stRef  = makeRef "st"
st1Ref = makeRef "st1"
st2Ref = makeRef "st2"
st3Ref = makeRef "st3"

asRef :: Ref [SLogic]
asRef = makeRef "as"

nRef, n1Ref, n2Ref, n3Ref :: Ref Int
nRef   = makeRef "n"
n1Ref  = makeRef "n1"
n2Ref  = makeRef "n2"
n3Ref  = makeRef "n3"

newtype Subgoals = Subgoals { fromSubgoals :: [Statement] }

subgoalsRef :: Ref Subgoals
subgoalsRef = makeRef "subgoals"

instance Reference Subgoals

instance Show Subgoals where
   show = intercalate ";" . map show . fromSubgoals

instance Read Subgoals where
   readsPrec _ s = 
      case mapM readM (splitsWithElem ';' s) of
         Just ys -> [(Subgoals ys, "")]
         Nothing -> []

instance IsTerm Subgoals where
   toTerm = toTerm . fromSubgoals
   termDecoder = Subgoals <$> termDecoder

----------------------------------------------------------------------
-- Parameterized rules

assumptionR :: Rule AxiomaticProof
assumptionR = ruleTrans assumpId $ 
   transInput1 phiRef $ \x -> Just . assumption x

assumptionCloseR :: Rule AxiomaticProof
assumptionCloseR = ruleTrans assumptionCloseId $ 
  transInput1 nRef assumptionClose

lemmaR :: Rule AxiomaticProof
lemmaR = ruleTrans lemmaId $ 
  transInput1 stRef $ \x -> Just . introLemma x

lemmaCloseR :: Rule AxiomaticProof
lemmaCloseR = ruleTrans lemmaCloseId $ 
   transInput1 nRef lemmaClose

axiomAR :: Rule AxiomaticProof
axiomAR = ruleTrans axiomAId $
   transInput2 phiRef psiRef $ \x y -> Just . introAxiomA x y
   
axiomACloseR :: Rule AxiomaticProof
axiomACloseR = ruleTrans axiomACloseId $
   transInput1 nRef axiomAClose

axiomBR :: Rule AxiomaticProof
axiomBR = ruleTrans axiomBId $
   transInput3 phiRef psiRef chiRef $ \x y z -> Just . introAxiomB x y z
 
axiomBCloseR :: Rule AxiomaticProof
axiomBCloseR = ruleTrans axiomBCloseId $
   transInput1 nRef axiomBClose
   
axiomCR :: Rule AxiomaticProof
axiomCR = ruleTrans axiomCId $
   transInput2 phiRef psiRef $ \x y -> Just . introAxiomC x y
   
axiomCCloseR :: Rule AxiomaticProof
axiomCCloseR = ruleTrans axiomCCloseId $
   transInput1 nRef axiomCClose

transInput6M :: Ref i1 -> Ref i2 -> Ref i3 -> Ref i4 -> Ref i5 -> Ref i6
             -> (Maybe i1 -> Maybe i2 -> Maybe i3 -> Maybe i4 -> Maybe i5 -> Maybe i6 -> a -> Maybe b) -> Trans a b
transInput6M r1 r2 r3 r4 r5 r6 f = 
   (identity &&& readRefMaybe6 r1 r2 r3 r4 r5 r6) >>> 
   transMaybe (\(a, (m1, m2, m3, m4, m5, m6)) -> f m1 m2 m3 m4 m5 m6 a)

readRefMaybe6 :: Ref a -> Ref b -> Ref c -> Ref d -> Ref e -> Ref f
              -> Trans x (Maybe a, Maybe b, Maybe c, Maybe d, Maybe e, Maybe f)
readRefMaybe6 r1 r2 r3 r4 r5 r6 = 
   (readRefMaybe r1 &&& readRefMaybe r2 &&& readRefMaybe r3 &&& readRefMaybe r4 &&& readRefMaybe r5 &&& readRefMaybe r6)
   >>> transPure (\(m1, (m2, (m3, (m4, (m5, m6))))) -> (m1, m2, m3, m4, m5, m6))

mpRule :: Rule AxiomaticProof
mpRule = ruleTrans mpId $ 
   transInput6M n1Ref n2Ref n3Ref st1Ref st2Ref st3Ref modusPonensForwardG
   
dedForwardR :: Rule AxiomaticProof
dedForwardR = siblingOf dedId $ ruleTrans dedForwardId $
   transInput2 nRef phiRef deductionForward

dedBackwardR :: Rule AxiomaticProof
dedBackwardR = siblingOf dedId $ ruleTrans dedBackwardId $
   transInput1 nRef deductionBackward

dedCloseR :: Rule AxiomaticProof
dedCloseR = siblingOf dedId $ ruleTrans dedCloseId $
   transInput2 n1Ref n2Ref deductionClose

goalR1 :: Rule AxiomaticProof
goalR1 = ruleTrans goalId1 $
   transInput1 stRef createGoal1
   
goalR :: Rule AxiomaticProof
goalR = ruleTrans goalId $
   transInput2 nRef stRef createGoal

renumberR :: Rule AxiomaticProof
renumberR = describe "Renumber proof lines" $
   makeRule (logax # "renumber") $ \p -> Just (renumber p)

removeLineR :: Rule AxiomaticProof
removeLineR = describe "Remove line number" $
   ruleTrans (logax # "removeline") $ 
   transInput1 nRef $ \n p -> Just (removeLine n p)

-----------------------------------------------------------------------

assumption :: SLogic -> AxiomaticProof -> AxiomaticProof
assumption phi = forward ([phi] |- phi) Assumption

introLemma :: Statement -> AxiomaticProof -> AxiomaticProof
introLemma st = forward st Lemma

introAxiomA :: SLogic -> SLogic -> AxiomaticProof -> AxiomaticProof
introAxiomA phi psi = forward (axiomA phi psi) AxiomA

introAxiomB :: SLogic -> SLogic -> SLogic -> AxiomaticProof -> AxiomaticProof
introAxiomB phi psi chi = forward (axiomB phi psi chi) AxiomB

introAxiomC :: SLogic -> SLogic -> AxiomaticProof -> AxiomaticProof
introAxiomC phi psi = forward (axiomC phi psi) AxiomC

assumptionClose :: Int -> AxiomaticProof -> Maybe AxiomaticProof
assumptionClose n prf = do
   st <- getTerm n prf
   let as = assumptions st
       cs = consequent st
   guard $ cs `S.member` as
   return $ addMotivation n Assumption prf   

lemmaClose :: Int -> AxiomaticProof -> Maybe AxiomaticProof
lemmaClose n prf = do
  t <- getTerm n prf
  guard $ any ((t ==) . instantiate) knownLemmas
  return $ addMotivation n Lemma prf

knownLemmas :: [Lemma]
knownLemmas = concatMap thd3 (exampleList ++ mmExampleList ++ wendyList ++ lemmaList)

axiomAClose :: Int -> AxiomaticProof -> Maybe AxiomaticProof
axiomAClose n prf = do
   st <- getTerm n prf
   let cs = consequent st      
   guard $ isAxiom cs 
   return  $ addMotivation n AxiomA prf
 where 
   isAxiom (p :->: (_ :->: r)) = p == r 
   isAxiom _ = False
   
axiomBClose :: Int -> AxiomaticProof -> Maybe AxiomaticProof
axiomBClose n prf = do
   st <- getTerm n prf
   let cs = consequent st      
   guard $ isAxiom cs 
   return  $ addMotivation n AxiomB prf  
 where 
   isAxiom ((p :->: (q :->: r)):->: ((s:->:t) :->: (u :->:v))) = p == s && p == u && q == t && r == v
   isAxiom _ = False 
   
axiomCClose :: Int -> AxiomaticProof -> Maybe AxiomaticProof
axiomCClose n prf = do
   st <- getTerm n prf
   let cs = consequent st      
   guard $ isAxiom cs 
   return  $ addMotivation n AxiomC prf  
 where 
   isAxiom ((p :->:q) :->:  (r :->: s)) = p == Not s && q == Not r
   isAxiom _ = False   

modusPonensForwardG :: Maybe Int -> Maybe Int -> Maybe Int
                    -> Maybe Statement -> Maybe Statement -> Maybe Statement 
                    -> AxiomaticProof -> Maybe AxiomaticProof
modusPonensForwardG mn1 mn2 mnc mst1 mst2 mstc prf = 
   case (mn1, mn2, mnc, mst1, mst2, mstc) of
      (Just n1, Just n2, Just nc, Just st1, Just st2, Just stc) -> 
         let mot = ModusPonens n1 n2
         in modusPonens mot (n1, st1) (n2, st2) (nc, stc) prf
      --------------------------------------------------------------------------
      -- Old (specialized rules)
      -- (Just n1, Just n2, Nothing, Just _, Just _, Just _) -> modusPonensForward n1 n2 prf
      -- (Just n1, Nothing, Just nc, _, _, _) -> modusPonensMiddle1 nc n1 prf
      -- (Nothing, Just n2, Just nc, _, _, _) -> modusPonensMiddle2 nc n2 prf
      -- (Just n1, Just n2, Just nc, _, _, _) -> modusPonensClose nc n2 n1 prf
      -- (Nothing, Nothing, Nothing, Just st1, Just st2, Just stc) -> modusPonensHint st1 st2 stc prf
      --------------------------------------------------------------------------
      -- Lookup number in proof (to find statement)
      (Just n1, _, _, Nothing, _, _) | isJust new ->
         modusPonensForwardG mn1 mn2 mnc new mst2 mstc prf
       where
         new = getTerm n1 prf
      (_, Just n2, _, _, Nothing, _) | isJust new ->
         modusPonensForwardG mn1 mn2 mnc mst1 new mstc prf
       where
         new = getTerm n2 prf
      (_, _, Just nc, _, _, Nothing) | isJust new ->
         modusPonensForwardG mn1 mn2 mnc mst1 mst2 new prf
       where
         new = getTerm nc prf
      --------------------------------------------------------------------------
      -- Combine two statements (to find third statement)
      (_, _, _, Just st1, Just st2, Nothing) ->
         case consequent st2 of 
            _ :->: psi ->
               let as  = assumptions st1 `S.union` assumptions st2
                   stc = as :|- psi
               in modusPonensForwardG mn1 mn2 mnc mst1 mst2 (Just stc) prf      
            _ -> Nothing
      (_, _, _, Just st1, Nothing, Just stc) ->
         let st2 = assumptions stc :|- consequent st1 :->: consequent stc
         in modusPonensForwardG mn1 mn2 mnc mst1 (Just st2) mstc prf
      (_, _, _, Nothing, Just st2, Just stc) ->
         case consequent st2 of
            phi :->: _ -> 
               let st1 = assumptions stc :|- phi
               in modusPonensForwardG mn1 mn2 mnc (Just st1) mst2 mstc prf
            _ -> Nothing
      --------------------------------------------------------------------------
      -- Lookup statement in proof (to find number)
      (Nothing, _, _, Just st1, _, _) | isJust new -> 
         modusPonensForwardG new mn2 mnc mst1 mst2 mstc prf
       where
         new = findInProof st1 prf
      (_, Nothing, _, _, Just st2, _) | isJust new -> 
         modusPonensForwardG mn1 new mnc mst1 mst2 mstc prf
       where
         new = findInProof st2 prf
      (Just n1, Just n2, Nothing, _, _, Just stc) | isJust new && fromJust new > n1 && fromJust new > n2 -> 
         modusPonensForwardG mn1 mn2 new mst1 mst2 mstc prf
       where
         new = findInProof stc prf
      --------------------------------------------------------------------------
      -- Auto number
      (Nothing, _, _, _, _, _) ->
         let n1 = prevNumberBefore (fromMaybe maxBound mnc) prf
         in modusPonensForwardG (Just n1) mn2 mnc mst1 mst2 mstc prf
      (_, Nothing, _, _, _, _) ->
         let n2 = prevNumberBefore (fromMaybe maxBound mnc) prf
         in modusPonensForwardG mn1 (Just n2) mnc mst1 mst2 mstc prf
      (_, _, Nothing, _, _, _) ->
         let f  = fromMaybe minBound
             nc = nextNumberAfter (f mn1 `max` f mn2) prf
         in modusPonensForwardG mn1 mn2 (Just nc) mst1 mst2 mstc prf
      --------------------------------------------------------------------------
      _ -> Nothing



modusPonens :: AxiomaticLabel Int -> (Int, Statement) -> (Int, Statement) -> (Int, Statement) -> AxiomaticProof -> Maybe AxiomaticProof
modusPonens mot (n1, st1) (n2, st2) (nc, stc)
   | conditions =
        (\p -> guard (not (isNotMotivated n1 p) && not (isNotMotivated n2 p)) >> Just p)
        >=> addStatement n1 st1 >=> addStatement n2 st2 
        >=> addStatement nc stc >=> addMotivation2 nc mot
   | otherwise =
        const Nothing   
 where
   conditions = n1 < nc && n2 < nc &&
      assumptions st1 `S.isSubsetOf` assumptions stc &&
      assumptions st2 `S.isSubsetOf` assumptions stc &&
      fits (consequent st1) (consequent st2) (consequent stc)
      
   fits p1 (p2 :->: q1) q2 = p1 == p2 && q1 == q2
   fits _ _ _ = False

addStatement :: (Functor l, Foldable l, Eq a) => Int -> a -> Proof l a -> Maybe (Proof l a)
addStatement n a p =
   case getTerm n p of
      Just b -> do
         guard (a == b)
         return p
      Nothing -> Just (proofgoal n a <> p)

-- changed this definition: no longer compares motivation labels and groundedness
addMotivation2 :: Int -> AxiomaticLabel Int -> AxiomaticProof -> Maybe AxiomaticProof
addMotivation2 n mot p = do
   guard (isNotMotivated n p)
   return (addMotivation n mot p)
      
deductionForward :: Int -> SLogic -> AxiomaticProof -> Maybe AxiomaticProof
deductionForward n phi prf = do
   st1 <- getTerm n prf
   guard (isMotivated n prf)
   let st  = (phi `S.delete` assumptions st1) :|- (phi :->: consequent st1)
   return (forwardAfter n st (Deduction n) prf)

deductionBackward :: Int -> AxiomaticProof -> Maybe AxiomaticProof
deductionBackward n prf = do
   guard (isNotMotivated n prf)
   st1 <- getTerm n prf
   (phi, psi) <- isImpl (consequent st1)
   let n1  = prevNumberBefore n prf
       new = proofgoal n1 (S.insert phi (assumptions st1) :|- psi)
   return $ new <> addMotivation n (Deduction n1) prf
 where
   isImpl (p :->: q) = Just (p, q)
   isImpl _ = Nothing

deductionClose :: Int -> Int -> AxiomaticProof -> Maybe AxiomaticProof
deductionClose n1 n2 prf = do
   guard (isNotMotivated n2 prf)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   p   <- fits (consequent st1) (consequent st2)
   guard (S.delete p (assumptions st1) `S.isSubsetOf` assumptions st2)
   return  $ addMotivation n2 (Deduction n1) prf 
 where
   fits q1 (p :->: q2) | q1 == q2 = Just p
   fits _ _ = Nothing

createGoal1 :: Statement -> AxiomaticProof -> Maybe AxiomaticProof
createGoal1 st prf 
   | validStatement st = Just $ proofgoal (prevNumber prf) st <> prf
   | otherwise = Nothing
  
createGoal :: Int -> Statement -> AxiomaticProof -> Maybe AxiomaticProof
createGoal n st prf 
   | validStatement st && not (st `subStatement` exgoal || exgoal `subStatement` st) = Just $ proofgoal n st <> prf
   | otherwise = Nothing
 where  
   exgoal = fromJust (getTerm 1000 prf)

--------------------------------------------------------------------------------

forward :: Statement -> AxiomaticLabel Int -> AxiomaticProof -> AxiomaticProof
forward st m prf = pl <> prf
 where
   n  = nextNumber prf
   pl = proofline n st m
   
forwardAfter :: Int -> Statement -> AxiomaticLabel Int -> AxiomaticProof -> AxiomaticProof
forwardAfter n1 st m prf = pl <> prf
 where
   n  = nextNumberAfter n1 prf
   pl = proofline n st m

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)