module Domain.Logic.Axiomatic.Exercise 
   ( logaxExercise, logaxStrategy
   ) where

import Control.Monad
import Data.Char 
import Data.Maybe
import Domain.Logic.Parser
import Domain.Logic.Axiomatic.Label
import Domain.Logic.Axiomatic.LinearProof
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.Lemma
import Domain.Logic.Axiomatic.Rules
import Domain.Logic.Axiomatic.BuggyRules
import Domain.Logic.Axiomatic.ProofGeneratorDAG (axiomaticStrategy, makeEnvWithDag, proofDag)
import Domain.Logic.Axiomatic.ExtractProof
import Domain.Logic.Axiomatic.ProofDAG
import Ideas.Common.Library hiding (check, label, lastTerm, traverse)
import Ideas.Encoding.Encoder
import qualified Data.Set as S
import qualified Ideas.Common.Library as Ideas
import Ideas.Text.JSON

data Axiomatic = AP { getProof :: AxiomaticProof, getLemmas :: Lemmas }

instance Show Axiomatic where
   show (AP p lem) = unlines (map show lem) ++ "\n" ++ show p

instance InJSON Axiomatic where
   toJSON (AP p lem) = Object [("proof", toJSON p), ("lemmas", toJSON lem)]
   jsonDecoder = jObject $ 
      AP <$> jKey "proof" jsonDecoder <*> jKey "lemmas" jsonDecoder

instance IsTerm Axiomatic where
   toTerm (AP p lem) = toTerm (p, lem)
   termDecoder = uncurry AP <$> termDecoder

axiomaticView :: View Axiomatic (AxiomaticProof, Lemmas)
axiomaticView = makeView (\(AP p lem) -> Just (p, lem)) (uncurry AP)

logaxExercise :: Exercise Axiomatic
logaxExercise = {- latexEncoding $ -} checkEnv $ jsonEncoding emptyExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.logax"
   , status         = Experimental
   , prettyPrinter  = show
   , parser         = fmap (`AP` []) . parseProof
   , suitable       = predicate (partialProof . getProof)
   , ready          = predicate (proofIsReady . getProof)
   , equivalence    = withoutContext (\x y -> equalProof (getProof x) (getProof y))
   , similarity     = withoutContext (\x y -> similarProof (getProof x) (getProof y))
   , hasTermView    = Just termView
   , strategy       = Ideas.label "logic.propositional.logax" (liftToContext logaxStrategy)
   , extraRules     = map (liftToContext . liftViewIn axiomaticView) $
                         [ assumptionR, assumptionCloseR
                         , axiomAR, axiomBR, axiomCR,axiomACloseR, axiomBCloseR, axiomCCloseR
                         , mpRule
                         , dedForwardR, dedBackwardR, dedCloseR
                         , goalR, renumberR, removeLineR, goalR1
                         , lemmaR, lemmaCloseR
                         ] ++ buggyRules
   , ruleOrdering   = ruleOrderingWith buggyRules
   , examples       = examplesWithDifficulty 
                         [ (dif, AP (proofgoal 1000 st) lem)
                         | (dif, st, lem) <- firstExamplesList ++ lemmaList ++ exampleList ++ mmExampleList  --    exampleList --
                         ]
   }

checkEnv :: Exercise a -> Exercise a 
checkEnv = setProperty "environment-check" check
 where
   check :: Environment -> Maybe String
   check env = listToMaybe $ 
      mapMaybe isLogic ["phi", "psi", "chi"] ++ mapMaybe isStatement ["st"]
    where
      isLogic     = checkWith parseLogicPars
      isStatement = checkWith (parseStatement False)

      checkWith :: (String -> Either String a) -> String -> Maybe String
      checkWith parseFun var = do
         txt <- makeRef var ? env
         case parseFun txt of
            Left msg -> Just $ var ++ ": " ++ msg -- report the syntax error
            Right _  -> Nothing

logaxStrategy :: Strategy Axiomatic
logaxStrategy = dynamic "logic.propositional.logax.generator" logaxStrategyGen

logaxStrategyGen :: Axiomatic -> Strategy Axiomatic
logaxStrategyGen ax = 
   liftViewIn axiomaticView $ extractProof grounded ungrounded goals $ trimProofDag goals $ trimMotivations dag
 where
   proof  = getProof ax
   plines = prooflines proof
   lemmas = getLemmas ax
   goals  = map (fst . snd) (filter unmotivated plines)
   env    = makeEnvWithDag (proofToDag proof) goals lemmas
   dag    = proofDag (applyD axiomaticStrategy env)
   
   grounded = termsInProof (keepGrounded proof)
   ungrounded = map (map (fst . snd)) $ splitBefore unmotivated plines
   
   unmotivated (_, (_, mot)) = isNothing mot
      
splitBefore :: (a -> Bool) -> [a] -> [[a]]
splitBefore p = rec . dropWhile (not . p)
 where
   rec []     = []
   rec (x:xs) = (x:xs1) : rec xs2
    where
      (xs1, xs2) = break p xs 

proofToDag :: (Traversable l, Ord (l a), Ord a) => Proof l a -> ProofDag l a
proofToDag p = mconcat (mapMaybe f (prooflines (keepGrounded p)))
 where
   f (_, (a, maybeMot)) = do
      mot <- maybeMot
      (a ==>) <$> traverse (`getTerm` p) mot

parseProof :: String -> Either String AxiomaticProof
parseProof s = 
   case rights (map parseProofline (filter (not . all isSpace) (lines s))) of
      Left err -> Left err
      Right xs -> Right (mconcat xs)
 where
   rights :: [Either a b] -> Either a [b]
   rights [] = Right []
   rights (Left a:_) = Left a
   rights (Right b:xs) = fmap (b:) (rights xs)

parseProofline :: String -> Either String AxiomaticProof
parseProofline s = 
   case span isDigit (dropWhile isSpace s) of 
      (nr, '.':s1) | not (null nr) -> 
         parseProoflineNr (read nr) s1
      _ -> -- use 1000 as default number
         parseProoflineNr 1000 s

parseProoflineNr :: Int -> String -> Either String AxiomaticProof
parseProoflineNr nr s = 
   case (parseStatement False s1, parseMotivation s2) of
      (Left err, _)         -> Left err
      (Right st, Right mot) -> Right $ proofline nr (mk st) mot
      (Right st, _)         -> Right $ proofgoal nr (mk st)
 where
   (s1, s2) = break (== '[') s
   mk (ps, q) = ps |- q

parseMotivation :: String -> Either String (AxiomaticLabel Int)
parseMotivation = maybe (Left "not a motivation") Right . readM

-- for now, we assume that the goal is in the last proof line
proofIsReady :: AxiomaticProof -> Bool
proofIsReady p = maybe False (`goalIsReached` p) (lastTerm p) && partialProof p

partialProof :: AxiomaticProof -> Bool
partialProof = -- we negeren voorlopig de motivatie
   all validStatement . termsInProof

goalIsReached :: Statement -> AxiomaticProof -> Bool
goalIsReached goal p = 
   isInProof goal p && fullyMotivated p

equalProof :: AxiomaticProof -> AxiomaticProof -> Bool
equalProof p1 p2 = fromMaybe False $ do
   t1 <- lastTerm p1 
   t2 <- lastTerm p2
   return $ t1 `similarStatement` t2 
      && partialProof p1 && partialProof p2

similarProof :: AxiomaticProof -> AxiomaticProof -> Bool
similarProof p1 p2 = and (zipWith similarProofline xs ys)
 where
   xs = prooflines (renumber p1)
   ys = prooflines (renumber p2)

similarProofline :: Eq mot => (Int, (Statement, mot)) -> (Int, (Statement, mot)) -> Bool
similarProofline (_, (t1, mot1)) (_, (t2, mot2)) = 
   similarStatement t1 t2 && mot1 == mot2

similarStatement :: Statement -> Statement -> Bool
similarStatement st1 st2 = 
   consequent st1 == consequent st2 && validStatement (xs :|- consequent st1)
 where
   -- door de intersectie nemen kun je assumpties introduceren waar je niet meer 
   -- vanaf komt. Eigenlijk zou hier op gecontroleerd moeten worden (in de 
   -- context van het bewijs).
   xs = assumptions st1 `S.intersection` assumptions st2

-------------------------------------------------------------------------
-- debug functions (use underscore in name)

_see :: Int -> IO ()
_see n = printDerivation logaxExercise (examplesAsList logaxExercise !! n)

_seel :: Int -> IO ()
_seel n = printDerivation logaxExercise (AP (proofgoal 1000 st) lems)
 where
   (_, st, lems) = lemmaList !! n

_seew :: Int -> IO ()
_seew n = printDerivation logaxExercise (AP (proofgoal 1000 st) lems)
 where
   (_, st, lems) = wendyList !! n

_seeold :: Int -> IO ()
_seeold n = printDerivation logaxExercise (AP (proofgoal 1000 st) lems) 
 where
   (_, st, lems) = exampleList !! n

-- N=60
-- Total length: 439
_go :: IO ()
_go = do
   is <- forM (examplesAsList logaxExercise) $ \a -> do
      case defaultDerivation logaxExercise a of
         Just d -> 
            return (derivationLength d)
         Nothing ->
            error $ "No solution for " ++ show a
   putStrLn $ "N=" ++ show (length is)
   putStrLn $ "Total length: " ++ show (sum is)

_t :: Axiomatic
_t = {- fromJust $ fromContext $ last $ terms $ fromJust $ defaultDerivation logaxExercise $ -} head $ examplesAsList logaxExercise