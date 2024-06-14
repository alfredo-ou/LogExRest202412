module Domain.Logic.Axiomatic.ProofGeneratorDAG 
   ( proofDag, makeEnvWithDag, axiomaticStrategy
   ) where

import Ideas.Utils.Prelude
import Data.List
import Data.Maybe
import qualified Data.Set as S
import Ideas.Common.Library
import qualified Ideas.Common.Library as Library
import Domain.Logic.Formula
import Domain.Logic.Axiomatic.Label
import Domain.Logic.Axiomatic.ProofDAG
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.Lemma

axiomaticDagExercise :: Exercise Env
axiomaticDagExercise = emptyExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic.dag"
   , status         = Experimental
   , prettyPrinter  = show
   , strategy       = Library.label "axiomatic" (liftToContext axiomaticStrategy)
   , examples       = examplesWithDifficulty[ (dif, makeEnv [goal] lems) | (dif, goal, lems) <- wendyList ]
   }
   
axiomaticStrategy :: Strategy Env
axiomaticStrategy = 
   untilS stop
 --   replicateS 80
 --      goalAvailable
       $ skipFalse
      -- |> lemmaRule
      |> elimGoal
      |> implicationIntro
      |> axiomBheuristic1 .*. repeatS modusPonens
      |> axiomBheuristic2 
      |> axiomBheuristic3 
      |> useImpl
      |> axiomCheuristic1 .*. modusPonens   
      |> axiomCheuristic3 .*. modusPonens
      |> axiomCheuristic2 .*. modusPonens
      |> modusPonens
      |> doubleNegation
      |> deduction
      |> falseAsGoal
      |> negAsGoal 
      |> skipFalse
      |> contradiction1S
      |> contradiction1a .*. deduction 
      |> contradiction2S
      |> contradiction3
  --    |> contradiction4a 
      |> contradiction4
      |> contradiction5
      |> contradiction6 .*. repeatS modusPonens |> deduction
      |> contradiction7
      |> useImplAssumption
      |> useNegatedContradiction
      |> useNegAssumption

 --     .*. trim
 where
   stop = null . goals 


-----------------------------------------------------------------
-- Sub-strategies

contradiction1S :: Strategy Env
contradiction1S =
        contradiction1 .*.  repeatS modusPonens .*. contradiction1seq -- .*. repeatS modusPonens

contradiction2S :: Strategy Env
contradiction2S = contradiction2 .*. contradiction2seq .*. repeatS modusPonens .*. contradiction1S


-----------------------------------------------------------------
         
data Env = Env 
   { goals    :: [Statement]
-- , lemma    :: Statement
   , proofDag :: ProofDag AxiomaticLabel Statement
   }
 deriving Eq
   
statements :: Env -> [Statement]
statements = proofterms . proofDag

consequents :: Env -> [SLogic] 
consequents = map consequent . statements

---------------------------------------------

assumption :: SLogic -> ProofDag AxiomaticLabel Statement
assumption p = [p] |- p ==> Assumption

lemma2 :: Statement -> ProofDag AxiomaticLabel Statement
lemma2 lem = lem ==> Lemma

axiomA2 :: SLogic -> SLogic -> ProofDag AxiomaticLabel Statement
axiomA2 phi psi = axiomA phi psi ==> AxiomA

axiomB2 :: SLogic -> SLogic -> SLogic -> ProofDag AxiomaticLabel Statement
axiomB2 phi psi chi = axiomB phi psi chi ==> AxiomB

axiomC2 :: SLogic -> SLogic -> ProofDag AxiomaticLabel Statement
axiomC2 phi psi = axiomC phi psi ==> AxiomC

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)

---------------------------------------------

lemmaRule :: SLogic -> Statement
lemmaRule phi = [] |- phi

makeEnvWithDag :: ProofDag AxiomaticLabel Statement -> [Statement] -> Lemmas -> Env
makeEnvWithDag dag gs lems = Env
   { goals    = gs
   , proofDag = lemmasList <> assumptionsList <> dag
   }
   where 
    assumptionsList = mconcat [ assumption p | (ps :|- _) <- gs, p <- S.toList ps] 
    lemmasList = mconcat (map (lemma2 . instantiate) lems) -- zo ook lemma's die geen tautologie zijn, niet mogelijk in webversie

makeEnv :: [Statement] -> Lemmas -> Env
makeEnv = makeEnvWithDag mempty

instance Show Env where
   show env = intercalate "\n"
      [ column "goals"  $ map show (goals env)
      , column "proofDag" $ lines (show (proofDag env))
      ]
    where
      column s xs = intercalate "\n" $ (s ++ ":") : map ("  " ++) xs
       
mmsee :: Int -> IO ()
mmsee i =  printDerivation axiomaticDagExercise (makeEnv [snd3 $ mmExampleList !! i] [])

see :: Int -> IO ()
see i =  printDerivation axiomaticDagExercise (makeEnv [snd3 $ exampleList !! i] (thd3 $ exampleList !! i))

modusPonens :: Rule Env
modusPonens = makeRule "modus-ponens" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = env { proofDag = proofDag env <> new } `extends` env
    where
      new = mconcat fs
      fs  = nubBy equalStatement [ st ==> ModusPonens a b
            | a <- filteredstatements -- statements env
            , b <- filteredstatements -- statements env
            , st  <- isMP a b
            , noCycle st a b
            , not (any (superStatement st) (statements env)) --  not (elem st (statements env))
            ]
                       
      isMP (as1 :|- p1) (as2 :|- p2 :->: q) | p1 == p2 =
         [ as1 `S.union` as2 :|- q ]
      isMP _ _ = []
      dag = proofDag env
      filteredstatements = filter nosuperStatement (statements env)
      noCycle p q r =
         p `S.notMember` (depends dag q `S.union` depends dag r)
      equalStatement t1 t2   = (fst $ (head (proofDagToList t1))) == (fst $ (head (proofDagToList t2)))   
      superStatement st1 st2 = subStatement st2 st1 && (st2 /= st1)
      nosuperStatement st = not (any (superStatement st) (statements env))

extends :: Env -> Env -> Maybe Env
extends new old 
   | proofDag new == proofDag old = Nothing
   | otherwise  = Just new

doubleNegation :: Rule Env
doubleNegation = makeRule "double-negation" trans
 where
   trans env 
      | null fs   = Nothing
      | otherwise = env { proofDag = proofDag env <> mconcat new }
           `extends` env
    where
      new = mconcat fs
      fs  =  [ [ axiomA2 con (Not (Not con)) 
               , axiomC2 (Not con) (Not pcon)
               , axiomC2 pcon con
               ]
            | st <- statements env
            , let con = consequent st
            , pcon <- isDoubleNeg con
            , all (\x -> not (x `subStatement` (assumptions st :|- pcon)))
                (statements env)
            ] 
            
      isDoubleNeg (Not (Not p)) = [p]
      isDoubleNeg _ = []


   
-- voegt een implicatie (via deductiestelling) toe aan de proofDag, en 
-- verwijdert de bijbehorende doelen
implicationIntro :: Rule Env
implicationIntro = makeRule "impl-intro1" trans
 where
   trans env@(Env ((as :|- p :->: q):gls) _) 
      | not newIsEmpty = Just env
           { goals = gls
           , proofDag = proofDag env <> new
           }
    where
      rs  = [ as :|- p :->: q ==> Deduction a
            | a <- statements env
            , let as1 :|- q1 = a
            , q1 == q
            , S.delete p as1 `S.isSubsetOf` as 
      --      , (S.insert p as :|- q1) `elem` statements env
            ]
   
      new = mconcat rs
      newIsEmpty = null $ proofterms new



   trans _ = Nothing
   
useImpl :: Rule Env
useImpl = makeRule "use-implication" trans
  where 
    trans env@(Env ((_ :|- r):_) _) 
       | cond = env {proofDag = proofDag env <> mconcat new} `extends` env            
          where
           new = [ st
                 | t1 <- statements env
                 , t2 <- statements env
                 , st <- fits (consequent t1) (consequent t2)
                 ]
           cond = not (null new)
           fits ((p :->: q) :->: x) s | q == s && x == r = [axiomA2 q p]
           fits _ _ = []
    trans _ = Nothing        

-- bewijs een doel mbv deductiestelling: voeg doel toe en voeg regels  toe aan 
-- het bewijs, als die er niet al in staan
deduction :: Rule Env
deduction = makeRule "deduction" trans
 where
   trans env@(Env (st@(as :|- p :->: q):gls) _) = Just
      env { goals = newst:st:gls
          , proofDag = proofDag env <> avp
          }
    where
      avp   = assumption p
      newst = addAssumption p (as :|- q)
   trans _ = Nothing 

   
-- doel bereikt: voeg motivatie toe als regel al in het bewijs staat, voeg 
-- anders regel + motivatie toe
elimGoal :: Rule Env
elimGoal = makeRule "elim-goal" trans
 where
   trans env@(Env ((as :|- p):gls) _)
      |  reached1 = Just env { goals = gls }
      |  reached  = Just env {goals = gls
                            ,proofDag = proofDag env <> newline}
    where
      reached1 =
         let ok3 (bs :|- q) = p == q && bs == as
         in any ok3 (statements env)
      reached = any ok2 (statements env)
      ok2 (bs :|- q) = p == q && bs `S.isSubsetOf` as
      new =  head $ filter ok2  (statements env)
      newline = (as :|- p) ==> findMotivation new (proofDag env)

   trans _ = Nothing
   
falseAsGoal :: Rule Env
falseAsGoal = makeRule "false-goal" trans
 where
   trans env@(Env ((as :|- p@(Var _)):_) _) 
      | p /= F = Just env
           { goals = addAssumption (Not p) (as :|- F) : goals env
           , proofDag = proofDag env <> new
           }
    where
      new = assumption (Not p)
   trans _ = Nothing

negAsGoal :: Rule Env
negAsGoal = makeRule "neg-goal" trans
 where
   trans env@(Env ((as :|- Not p):(_ :|- q):_) _) | q/= F = Just env
      { goals = addAssumption p (as :|- F) : goals env 
      , proofDag = proofDag env <> new
      }
      where
       new = assumption p
   trans env@(Env ((as :|- Not p):_) _)  = Just env
      {goals = addAssumption p (as :|- F) : goals env 
      , proofDag = proofDag env <> new
      } 
     where
       new = assumption p
   trans _ = Nothing



--   bewijs van p uit Not p -> p
contradiction1 :: Rule Env
contradiction1 = makeRule "contradiction1" trans
 where
  trans env@(Env ((as :|- F):st2@(_ :|- p):gls) _) 
      | cond  = Just env
           { goals = st2:gls    -- error "hier"
           , proofDag =  proofDag env <> mconcat newav
           } 
    where         
       cond = (Not p :->: p) `elem` 
          [ consequent st
          | st <- statements env
          , S.isSubsetOf (assumptions st) as 
          ]  
       newav = [ axiomA2 (Not p) (Not (Not (Not p :->: p))) 
               , axiomC2 (Not (Not p :->: p)) p
               , axiomC2 p (Not p :->: p)
               , axiomB2 (Not p) p (Not (Not p :->: p))
               ]      
  trans _ = Nothing    

 -- bewijs van |- Not p -> p uit Not p |- p
contradiction1a :: Rule Env
contradiction1a = makeRule "contradiction1a" trans
 where
  trans env@(Env ((as :|- F):(cs :|- p):_) _) 
      | cond  = Just env
           { goals = (cs:|- Not p :->: p) : goals env
           }
    where         
      cond = any ok (statements env)
      ok (bs :|- q) = q == p && bs `S.isSubsetOf` as  && Not p `S.member` bs

  trans _ = Nothing      
  
contradiction1seq :: Rule Env
contradiction1seq = makeRule "contradiction1seq" trans
 where
  trans env@(Env(st@(_ :|- p):gls) _) 
          = Just env
           { goals = st:gls
           , proofDag =  proofDag env <> head newav
           }
    where         
        newav = [ S.empty :|- Not p :->: p :->: Not (Not p :->: p) ==> Deduction t
                | t <- statements env
                , let as1 :|- q1 = t
                , q1 == (p :->: Not (Not p :->: p)) && as1 == S.singleton (Not p)
                ]
  trans _ = Nothing 
  
--  Bewijs van p uit Not p -> Not Not p 
contradiction2 :: Rule Env
contradiction2 = makeRule "contradiction2" trans
 where
  trans env@(Env ((_ :|- F):(_ :|- p):_) _) 
      | cond  = Just env
           {  
           proofDag = proofDag env <> newav
           }
    where         
       cond = (Not  p :->: Not (Not p)) `elem` consequents env
       newav = assumption (Not (Not p))
              
  trans _ = Nothing    
                     
contradiction2seq :: Rule Env
contradiction2seq = makeRule "contradiction2seq" trans
 where
  trans env@(Env ((_ :|- F):(_ :|- p):_) _) 
      | cond  = Just env
           { proofDag = proofDag env <> newav
           }
    where         
       cond = (Not  p :->: Not (Not p)) `elem` consequents env
       newav = axiomC2 p (Not p)
              
  trans _ = Nothing    

-- bewijs van Not p uit p -> Not p  
contradiction3 :: Rule Env
contradiction3 = makeRule "contradiction3" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):_) _) 
      | cond  = Just env
           {goals = [ bs :|- Not (Not p) :->: Not p, as :|- F, bs :|- Not p ] 
           }
    where         
       cond = (p :->: Not p) `elem` consequents env
  trans _ = Nothing    
  
-- bewijs van p uit  |- q en |- Not q  
contradiction4a :: Rule Env
contradiction4a = makeRule "contradiction4a" trans
 where
  trans env@(Env ((as :|- F):(bs :|- p):gls) _) 
      | cond  = Just env
           { goals = [  bs  :|- Not p :->: Not q
                     , as :|- F
                     , bs :|- p
                     ] <> gls
                    
           , proofDag = proofDag env <> newav 
           }
    where         

      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union  (assumptions t1) (assumptions t2)
            , zs `S.isSubsetOf` bs 
            ]
      newav = axiomC2 p q
      fits p1  (Not p2) = p1 == p2
      fits _ _ = False            
  trans _ = Nothing      

-- bewijs van Not p uit p |- q en |- Not q  
contradiction4 :: Rule Env
contradiction4 = makeRule "contradiction4" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):gls) _) 
      | cond1 = Just env
           { goals = [ bs :|- Not (Not p) :->: Not (Not q)
                     , bs :|- Not q :->: Not p
                     , bs :|- Not p 
                     ] ++ gls
           , proofDag = proofDag env <> newav1 
           }
      | cond  = Just env
           { goals = [ S.union bs (S.singleton (Not (Not p))) :|- q
                     , S.empty  :|- Not(Not (Not q)) :->: Not q
                     , as :|- F
                     , bs :|- Not p
                     ] <> gls
                    
           , proofDag = proofDag env <> newav 
           }
    where         
      cond1 = cond && ([] |- Not(Not (Not q)) :->: Not q) `elem` statements env
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (S.delete p (assumptions t1)) (assumptions t2)
            , zs `S.isSubsetOf` bs 
            ]
      newav1 = axiomC2 (Not(Not q)) q
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False 
      newav = assumption (Not (Not p))                    
  trans _ = Nothing      

-- bewijs van Not p uit |- q en p |- Not q  -- weglaten q uit bs nog controleren!
contradiction5 :: Rule Env
contradiction5 = makeRule "contradiction5" trans
 where
  trans env@(Env ((_ :|- F):(bs :|- Not p):gls) _) 
      | cond  = Just env
           { goals = [ bs :|-  Not (Not p) :->: Not q
                     , S.delete q bs :|- q :->: Not p
                     , bs :|- Not p
                     ] <> gls
           }
    where         
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (assumptions t1) (S.delete p (assumptions t2))
            , zs `S.isSubsetOf` bs 
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False         
  trans _ = Nothing        

  
-- bewijs van p uit Not p |- q,  Not p |- Not q  
contradiction6 :: Rule Env
contradiction6 = makeRule "contradiction6" trans
 where
  trans env@(Env ((_ :|- F):(bs :|- p):_) _) 
      | cond  = Just env
           { goals = [ S.insert (Not p) bs :|- q :->:  p
                     , S.insert (Not p) bs :|- p
                     , bs :|- Not p :->:  p 
                     ] ++ goals env
           , proofDag = proofDag env <> newav1 <> newav2
           }
    where         
      cond = not(null new)
      q = head new
      newav1 = axiomC2 p q
      newav2 = axiomA2 (Not q) (Not p)
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (Not p)
                     $ S.union (assumptions t1) (assumptions t2)
            , zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2 && p1 /= Not p && p /= Not p1
      fits _ _ = False         
  trans _ = Nothing         

     
-- bewijs van Not p uit p |- q,  p |- Not q  
contradiction7 :: Rule Env
contradiction7 = makeRule "contradiction7" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):_) _) 
     | cond  = Just env
           {  goals = [ S.insert (Not (Not p)) bs :|-  q
                      , S.insert (Not (Not p)) bs :|- Not q
                      , bs :|- q :->: Not p
               --     , as :|- F
               --     , bs :|- Not p  
                      ] ++ goals env
           , proofDag = proofDag env <> newav
           }
    where         
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete p $ S.union (assumptions t1) (assumptions t2)
            , zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False   
      newav = assumption (Not (Not p))
  trans _ = Nothing      

axiomBheuristic1 :: Rule Env
axiomBheuristic1 = makeRule "axiomBheuristic1" trans
 where
    trans env@(Env ((as :|- (p1 :->: q) :->: (p2 :->: r)):_) _) 
     | p1 == p2 && cond   = Just env
                { 
                 proofDag = proofDag env <> newav 
                }
     where               
      newav = axiomB2 p1 q r
      cond = (p1 :->: (q :->: r)) `elem`
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    
    
-- geprobeerd om de heuristiek na deductiestelling toe te laten passen (dus op tweede ipv eerste goal), maar dat geeft problemen met goal reached
axiomBheuristic2 :: Rule Env
axiomBheuristic2 = makeRule "axiomBheuristic2" trans
 where
    trans env@(Env ((as :|- (p2 :->: r2)):_) _)
     | cond   = Just env
                { 
                 proofDag = proofDag env <> newav1 <> newav2 
                }
     where               
      newav1 = axiomB2 p2 (head qList) r2
      newav2 = axiomA2 (head qList) p2
      cond = not (null qList) 
              &&  (head (proofterms newav1) `notElem` statements env)
      qList = catMaybes 
                 [ qFromCons (consequent st)
                 | st <- statements env
                 , S.isSubsetOf (assumptions st) as
                 ]
      qFromCons (p1 :->: (q :->: r1)) | p1 == p2 && r1 == r2 = Just q
      qFromCons _ = Nothing

    trans _ = Nothing 

axiomBheuristic3 :: Rule Env
axiomBheuristic3 = makeRule "axiomBheuristic1" trans
 where
    trans env@(Env ((as :|- (p1 :->: q) :->: (p2 :->: r)):_) _) 
     | p1 == p2 && cond   = env
                { 
                 proofDag = proofDag env <> newav 
                } `extends` env
     where               
      newav = axiomB2 p1 q r
      cond = (q :->: r) `elem`
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    

axiomCheuristic1 :: Rule Env
axiomCheuristic1 = makeRule "axiomCheuristic1" trans
 where
    trans env@(Env ((as :|- p :->: q):_) _)
     | cond   = env
                { 
                 proofDag = proofDag env <> newav 
                }  `extends` env
     where               
      newav = axiomC2 q p      
      cond = (Not q :->: Not p) `elem` 
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    
    
axiomCheuristic2 :: Rule Env
axiomCheuristic2 = makeRule "axiomCheuristic2" trans
 where
    trans env@(Env ((as :|- p :->: q):_) _) 
     | cond   = Just env
                {
                 proofDag = proofDag env <> newav1 <> newav2 
                }
     where               
      newav1 = axiomC2 q p
      newav2 = axiomA2 (Not p) (Not q)
      cond   = axiomC q p `notElem` statements env && Not p `elem` 
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    
    
axiomCheuristic3 :: Rule Env
axiomCheuristic3 = makeRule "axiomCheuristic3" trans
 where
    trans env@(Env ((_ :|- p :->: q):_) _) 
     | cond   = Just env
                {
                 proofDag = proofDag env <>  newav1 <> newav2 <> newav3
                }
     where     
       cond   = axiomC q p `notElem` statements env && not (null new)    
       new    = [  st             
                | st <- statements env
                , consequent st == Not p
                , Not q `S.member` assumptions st
                ]   
       newav1 = axiomC2 q p
       newav2 = axiomA2 (Not p) (Not q)
       newav3 = mconcat (map f new)
         where f x = S.delete (Not q) (assumptions x) :|- Not q :->: Not p ==> Deduction x
  --     [head new] ==> S.delete (Not q) (assumptions (head new)) :|- Not q :->: Not p $ Deduction
    trans _ = Nothing   

--  bewijs van contradictie door aantonen van tautologie |- phi als as |- niet phi in dag
useNegatedContradiction :: Rule Env
useNegatedContradiction = makeRule "negatedContradiction"  trans
  where
    trans env@(Env ((as :|- F):_) _) 
     | cond  = Just env
           {  goals = [
                       newgoal 
                      ] ++ goals env
           }
       where newgoal = fromJust $ g $ head  $ filter f (statements env)
             cond = not $ null (filter f (statements env))
             f (ps :|- Not q) = S.isSubsetOf ps as &&  (validStatement (S.empty :|- q))
             f _ = false
             g (ps :|- Not q)  = Just (S.empty :|-  q) 
             g _ = Nothing
    trans _ = Nothing


skipFalse :: Rule Env
skipFalse = makeRule "skipFalse" trans
 where
  trans env@(Env ((_ :|- F):st:gls) _) 
      | cond  = Just env { goals = st:gls }
         where         
         cond =  any ( `subStatement` st) (statements env)
 
  trans _ = Nothing       
    
   
useImplAssumption :: Rule Env
useImplAssumption = makeRule "impl-assumption" trans
 where
   trans env = rec (filter notExtra (statements env))
    where
      rec [] = Nothing
      rec ((_bs :|- p :->: _q):_) | notUsed (as :|- p) env = Just env
         { 
           goals = (f (p :->: _q) p (goals env) :|- p) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []        -> S.empty
              (bs :|- _):_ -> bs
                            
      f i t ((_ :|- F): (cs :|- _):_) | validStatement (S.delete i cs:|- t)  = S.delete i cs
      f i _ ((bs :|- _):_) = S.delete i bs
      f _ _ [] = S.empty

      notExtra st = isAssumption st && any  (S.isSubsetOf (assumptions st) . assumptions) (goals env)
    
notUsed :: Statement -> Env -> Bool
notUsed st env = all f (goals env) && all g (statements env)
   where
      f goal = not (goal `subStatement` st)
      g a    = not (a `subStatement` st)
    
isAssumption :: Statement -> Bool
isAssumption (qs :|- p) = p `S.member` qs
      
useNegAssumption :: Rule Env
useNegAssumption = makeRule "neg-assumption" trans
 where
   trans env = rec (filter isAssumption (statements env))
    where
      rec [] = Nothing
      rec ((_bs :|- Not p):_) | ((notUsed (as :|- p) env) && validStatement (as :|- p) && bevat (as :|- p)) = Just env
         { goals = (as :|- p) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []           -> S.empty
              (bs :|- _):_ -> bs

     

bevat :: Statement -> Bool
bevat (as :|- p)    = all (`elem` (  concat $ map varsLogic (S.toList as))) (varsLogic p) 

substatementInProof :: Statement -> ProofDag AxiomaticLabel Statement -> Bool
substatementInProof x p = 
   any (`subStatement` x) (proofterms p)