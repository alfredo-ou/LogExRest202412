module Domain.Logic.Axiomatic.ExtractProof 
   ( GoalStack, Grounded, Ungrounded
   , extractProof
   ) where

import Control.Arrow
import Control.Monad
import Data.Foldable
import Data.List (nub, partition, minimumBy)
import Data.Maybe
import Domain.Logic.Axiomatic.Label
import Domain.Logic.Axiomatic.LinearProof
import Domain.Logic.Axiomatic.ProofDAG
import Domain.Logic.Axiomatic.Rules (AxiomaticProof, Subgoals(..), mpRule, st1Ref, st2Ref, st3Ref, subgoalsRef)
import Domain.Logic.Axiomatic.Statement
import Ideas.Common.Library hiding (traverse)
import qualified Data.Set as S

type GoalStack = [Statement]

pushGoals :: [Statement] -> GoalStack -> GoalStack
pushGoals gs st = reverse $ nub $ reverse $ gs ++ st

removeGoal :: Statement -> GoalStack -> GoalStack
removeGoal a = filter (not . (a `subStatement`))

-- Een goal is een statement dat nog niet gemotiveerd is
-- Hou de volgende prioritering aan:
--
-- 1) sluiten van een bewijs voor een goal
--    -> motivatie toevoegen (als er meer zijn, kies voor laagste nr in bewijs)
-- 2) achteruit stappen (deductie stelling altijd een goed idee, MP niet zo heel gauw)
--    -> kies voor laatst toegevoegd (dus laagste nr in bewijs)
-- 3) gebruiken van statements die er al zijn (voorwaartse stap, is bijna altijd MP en niet Ded)
--    -> combineer regels die het laatst zijn toegevoegd (dus met hoogste nr; 1+4 beter dan 2+3)
-- 4) introduceren van een assumptie/axioma (lage prioriteit), dat zijn de regels zonder afhankelijkheid
--    -> welke ga ik gebruiken? slim zijn!
--          pak het laatst toegevoegde, gemotiveerde knoop (met hoogste nr)
--          kijk 1 stap vooruit, en vanuit daar wat je aan assumpties nodig hebt
--          

type Grounded = [Statement]

removeGrounded :: Grounded -> ProofDag AxiomaticLabel Statement -> ProofDag AxiomaticLabel Statement
removeGrounded grounded = filterNode (`notElem` grounded)

-- record which statements are ungrounded, and which statements become grounded together
-- the first elements of the lists are the unmotivated statements
type Ungrounded = [[Statement]]

ungroundedFirsts :: Ungrounded -> [Statement]
ungroundedFirsts = mapMaybe listToMaybe

ungroundedMove :: Statement -> Ungrounded -> ([Statement], Ungrounded)
ungroundedMove a xss = (concat yss, zss)
 where
   (yss, zss) = partition ((== [a]) . take 1) xss

ungroundedFrom :: Statement -> Statement -> Ungrounded -> Ungrounded
ungroundedFrom old new xss = 
   case break ((== [old]) . take 1) xss of
      (yss, []) -> yss ++ [[new]]
      (yss, zs:zss) -> yss ++ ((new:zs) : zss)

ppList :: Show a => String -> [a] -> String
ppList s xs = unlines (s : map show xs)

-- grounded:  bottom-up proof lines
-- ungrounded: top-down proof lines (goals)
extractProof :: Grounded -> Ungrounded -> [Statement] -> ProofDag AxiomaticLabel Statement -> Strategy AxiomaticProof
extractProof grounded ungrounded goals dag = try

   ( choice [ closeStep x | x <- closes ] ./.
     choice [ backwardStep x | x <- backws1 ] ./. 
     choice [ backwardStep x | x <- backws2 ] ./. 
     choice [ forwardStep x | x <- forws11 ] ./. 
     choice [ forwardStep x | x <- forws12 ] ./.
     choice [ forwardStep x | x <- forws21 ] ./. 
     choice [ forwardStep x | x <- forws22 ] ./. 
     choice [ introStep "(leafs 1)" x | x <- leafs11 ] ./. 
     choice [ introStep "(leafs 2)" x | x <- leafs12 ] ./. 
     choice [ introStep "(leafs 3)" x | x <- leafs21 ] ./.
     choice [ introStep "(leafs 4)" x | x <- leafs22 ] ./.
     choice [ forwardStep x | x <- forwsd1 ] ./. 
     choice [ forwardStep x | x <- forwsd2 ]  
   )
  
 where
   introStep s (a, mot) = 
      let newGoals = removeGoal a $ pushGoals (subgoals a) goals
              -- msg is for debugging only
          msg    = "\n==>>" ++ s ++ "\n" ++ ppList "GROUNDED" grounded ++ 
                   ppList "UNGROUNDED" ungrounded ++ ppList "GOALSTACK" goals ++
                   ppList "NEXTNODES" (proofDagToList nextDag) ++ ppList "LEAVES" leafs ++ ppList "FORWS" forws ++ ppList "FORWSDEEP" forwsdeep     -- nextNodes
                   ++ "\n" 
      in intro msg a mot (subgoalsForHints ungrounded newGoals) .*. extractProof (a:grounded) ungrounded newGoals dag

   forwardStep (a, mot) =
      let newGoals = removeGoal a goals
      in forward a mot (subgoalsForHints ungrounded goals) .*. extractProof (a:grounded) ungrounded newGoals dag
      
  -- hierboven dag ipv newDag zodat de nie
 
   backwardStep (a, mot) = 
      let newGoals = removeGoal a (pushGoals (toList mot) goals)
          newUngr = ungroundedFrom a (head $ toList mot) ungrounded
      in backward a mot (subgoalsForHints newUngr newGoals) .*. extractProof grounded newUngr newGoals dag

   closeStep (a, mot) =
      let newGoals = removeGoal a goals
          (grAs, newUngr) = ungroundedMove a ungrounded
      in close a mot (subgoalsForHints ungrounded newGoals) .*. extractProof (grAs ++ grounded) newUngr newGoals dag
      
   subgoalsForHints u = Subgoals . filter (`notElem` concat u)
 
   partially = grounded ++ concat ungrounded
   closes = [ (a, mot) 
            | (a, mot) <- proofDagToList dag
            , a `elem` ungroundedFirsts ungrounded
            , all (`elem` grounded) (toList mot)
            ]

   -- backward rules: backws1 are the rules that continue with the last ungrounded goal
   backws = [ (a, mot) 
            | (a, mot) <- proofDagToList dag
            , length (toList mot) == 1
            , a `elem` ungroundedFirsts ungrounded
            , all (`notElem` partially) (toList mot)
            ]
   (backws1, backws2) = partition backwWithUngrounded backws
   
   -- forward rules: forws1 are the rules that use the last proofline
   forws| null ungrounded = []
        | otherwise =         
             [ (a, mot) 
             | (a, mot) <- proofDagToList dag
             , not (null (toList mot))
             --       , a `notElem` partially
             , a `notElem` grounded
             , all (`elem` grounded) (toList mot)
             , not (any  (`subStatement` a) grounded)
             , head grounded `elem` toList mot
             ]
   (forws1, forws2) = partition forwWithGrounded forws
   (forws11, forws12) = partition noExtraAssumptions forws1
   (forws21, forws22) = partition noExtraAssumptions forws2   
   forwsdeep | null ungrounded = []
             | otherwise =  
                  [ (a, mot) 
                  | (a, mot) <- proofDagToList dag
                  , not (null (toList mot))
                  , a `notElem` partially
                  , all (`elem` grounded) (toList mot)
                  , not (any  (`subStatement` a) grounded)
           ]
   (forwsd1, forwsd2) = partition forwWithGrounded forwsdeep
   
   -- trimmed DAG for top of goal stack
   subDag = trimProofDag (take 1 goals) dag
   -- assumptions & axioms: leafs1 are the leafs that are needed to make progress
   leafs | null ungrounded =  [] 
         | otherwise =   [ (a, mot) | (a, mot) <- proofDagToList subDag, null (toList mot), a `notElem` grounded, S.size (assumptions a) < 2] -- assumptions met meer dan 1 aanname alleen als close step introduceren
   (leafs1, leafs2) = partition ((`elem` nextNodes). fst) leafs
   (leafs11, leafs12) =  partition ((`inAssumptions` (ungroundedFirsts ungrounded ++ lastSafe goals)) . fst) leafs1 
   (leafs21, leafs22) = partition ((`inAssumptions` (ungroundedFirsts ungrounded ++ lastSafe goals)) . fst) leafs2 
   subgoals a = calculateSubGoals a grounded (ungroundedFirsts ungrounded) dag
   -- 
   nextDag   = trimProofDag (take 1 goals) (removeGrounded grounded dag)
   nextNodes = proofterms nextDag
   --
   forwWithGrounded (_, mot) = 
      case grounded of
         hd:_ -> hd `elem` toList mot
         []   -> True

   backwWithUngrounded (a, _) =
      case ungroundedFirsts ungrounded of 
         hd:_ -> hd == a
         []   -> True
         
   noExtraAssumptions (a, mot)  = assumptions a `S.isSubsetOf` allAssumptions (toList mot)
    where
      allAssumptions = S.unions . map assumptions

lastSafe :: [a] -> [a]
lastSafe = take 1 . reverse
      
-------------------------------------------------------------------------------------------   

close :: Statement -> AxiomaticLabel Statement -> Subgoals -> Rule AxiomaticProof
close stc mot@(ModusPonens st1 st2) subgoals = 
   ruleTrans mot $
      (identity &&& (arr (const (st1, st2, stc, subgoals)) >>> writeRef4 st1Ref st2Ref st3Ref subgoalsRef)) >>> arr fst >>> transformation mpRule
close a mot subgoals = ruleTrans mot $ 
   (identity &&& (arr (const subgoals) >>> writeRef subgoalsRef)) >>> arr fst >>> transMaybe f
 where
   f p =
      case filter keep (prooflines p) of
         [] -> Nothing
         (goalnr, _):_ -> do
            newMot <- traverse (`findInProof` p) mot
            guard (all (< goalnr) (toList newMot))
            return $ addMotivation goalnr newMot p      

   keep (_, (b, mm)) = a == b && isNothing mm

-- x is the single assumption !!
backward :: Eq a => a -> AxiomaticLabel a -> Subgoals -> Rule (Proof AxiomaticLabel a)
backward a mot@(Deduction x) subgoals = ruleTrans mot $ 
   (identity &&& (arr (const subgoals) >>> writeRef subgoalsRef)) >>> arr fst >>> transMaybe f
 where
   f p = do
      goalnr <- findInProof a p
      guard (isNotMotivated goalnr p)
      let i = prevNumberBefore goalnr p
      return $ proofgoal i x <> addMotivation goalnr (Deduction i) p

-- msg is passed for debugging only
intro :: String -> Statement -> AxiomaticLabel Statement -> Subgoals -> Rule AxiomaticProof
intro msg a mot subgoals = ruleTrans mot $
   (identity &&& (arr (const subgoals) >>> writeRef subgoalsRef)) >>> arr fst >>> transMaybe f 
 where
   f p = do
      let i = nextNumber p
      newMot <- traverse (`findInProof` p) mot
      return $ proofline i a newMot <> p

forward :: Statement -> AxiomaticLabel Statement -> Subgoals -> Rule AxiomaticProof
forward stc mot@(ModusPonens st1 st2) subgoals = 
   ruleTrans mot $
      (identity &&& (arr (const (st1, st2, stc, subgoals)) >>> writeRef4 st1Ref st2Ref st3Ref subgoalsRef)) >>> arr fst >>> transformation mpRule
-- als een ongemotiveerde regel een motivatie krijgt, kunnen ook meer regels verhuizen naar grounded; dat lijkt nu niet op te lossen
-- op het niveau van de newGen, vandaar dat ik het hier heb toegevoegd.
forward a mot subgoals = ruleTrans mot $ 
   (identity &&& (arr (const subgoals) >>> writeRef subgoalsRef)) >>> arr fst >>> transMaybe f 
 where 
   f p = do
      guard (not (fullyMotivated p))
      newMot <- traverse (`findInProof` p) mot
      let i = nextNumberAfter (maximum (0 : toList newMot)) p
      return $ proofline i a newMot <> p

calculateSubGoals :: Statement -> [Statement] -> [Statement] -> ProofDag AxiomaticLabel Statement -> [Statement]
calculateSubGoals st grounded ungrounded dag = tail (filterSubGoals st subGoals)
 where
   subGoals = case search st of
                 path:_ -> path
                 []     -> []
   peers b xs = filter (`subStatement` b) (map fst xs)
   minimal b xs = minimumBy assumptionSize (peers b xs)
   assumptionSize x y = compare (S.size (assumptions x))   (S.size (assumptions y))
   search a
      | a `elem` grounded   = []
      | a `elem` ungrounded = [[]]
      | otherwise =
           [ minimal b (proofDagToList dag) : rest | (b, mot) <- proofDagToList dag, a `elem` toList mot, rest <- search b ]

filterSubGoals ::  Statement -> [Statement] -> [Statement]      
filterSubGoals st goals = rec (st : goals)
  where
    rec [] = []
    rec [a] = [a]
    rec (a:as) = a : rec (deleteSubStatements a as)

deleteSubStatements :: Statement -> [Statement] -> [Statement]  
deleteSubStatements st = filter (not . subStatement st)

inAssumptions :: Statement -> [Statement] -> Bool
inAssumptions = any . inAssumption
 where 
   inAssumption (_ :|- p) (qs :|- _) = p `elem` qs

-- to do: move to framework
writeRef4 :: Ref a -> Ref b -> Ref c -> Ref d -> Trans (a, b, c, d) (a, b, c, d)
writeRef4 r1 r2 r3 r4 = from4 ^>> writeRef2 r1 r2 *** writeRef2 r3 r4 >>^ to4
 where
   from4 (a, b, c, d) = ((a, b), (c, d))
   to4 ((a, b), (c, d)) = (a, b, c, d)