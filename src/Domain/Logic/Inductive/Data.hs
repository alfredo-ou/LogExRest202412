module Domain.Logic.Inductive.Data where

import Control.Applicative
import Data.Char
import Data.Either
import Data.Maybe
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.Theorem
import Domain.Logic.Inductive.Parser
import Ideas.Common.Id
import Ideas.Text.JSON
import Ideas.Utils.Prelude (readM)
import Ideas.Common.Rewriting
import Domain.Math.Expr hiding ((.*.), (./.))
import Domain.Algebra.Boolean
import Domain.Logic.Inductive.Symbols
import Ideas.Utils.Uniplate
import qualified Domain.Logic.Formula as Logic

------------------------------------------------------------------------------
-- Inductive

type RelProof = GRelProof Expr

type Active = Maybe ProofStep

-- active should not be a userstep
data Inductive = In
   { active  :: Active
   , proofs  :: [(Maybe ProofStep, RelProof)]
   , initial :: Initial
   }
 deriving (Show, Eq)

data ProofStep = BaseStep String | IHStep MetaVar | InductiveStep Case | UserStep String (Maybe ProofStep)
 deriving (Show, Eq, Ord)

instance IsTerm Inductive where
   toTerm a = toTerm ((active a, proofs a), initial a)
   termDecoder = (\((x1, x2), y) -> In x1 x2 y) <$> termDecoder
 
instance InJSON Inductive where
   toJSON a = Object $ 
      initialObject (initial a) ++ 
      [ ("active", maybe Null (String . proofStepToKey) (active a))
      , ("proofs", Object [ (maybe "" proofStepToKey ps, toJSON rp) | (ps, rp) <- proofs a ]) 
      ]
   jsonDecoder = inferCases <$> jObject (In <$> activeDecoder <*> proofsDecoder <*> jsonDecoder)

instance IsTerm ProofStep where
   toTerm (UserStep s ps) = toTerm (s, ps)
   toTerm ps = toTerm (proofStepToKey ps)

   termDecoder = do
         (s, ps) <- termDecoder
         return (UserStep s ps)
      <|> do 
         key <- termDecoder
         case keyToProofStep key of
            Just a  -> return a
            Nothing -> errorStr "not a proofstep"

instance IsId ProofStep where
   newId (BaseStep s)      = "basestep" # s
   newId (IHStep v)        = "ihstep" # v
   newId (InductiveStep c) = "inductivestep" # c
   newId (UserStep _ ps)   = newId ps

makeInductive :: Initial -> Inductive
makeInductive = In Nothing []

setActive :: Maybe ProofStep -> Inductive -> Inductive
setActive mps ind = ind
   { active = case mps of 
                 Just (UserStep _ this) -> this
                 _ -> mps
   } 

activeDecoder :: DecoderJSON Active
activeDecoder = jKey "active" (keyToActive <$> jString) <|> pure Nothing

proofsDecoder :: DecoderJSON [(Maybe ProofStep, RelProof)]
proofsDecoder = jKey "proofs" (jObjectWithKeys f)
 where 
   f k = (,) (keyToProofStep k) <$> proofDecoder exprDecoder

proofStepToKey :: ProofStep -> Key
proofStepToKey (BaseStep s)      = s
proofStepToKey (IHStep mv)       = mv
proofStepToKey (InductiveStep c) = show c
proofStepToKey (UserStep s _)    = s

keyToActive :: Key -> Maybe ProofStep
keyToActive = notUserStep . keyToProofStep
 where
   notUserStep (Just (UserStep _ _)) = Nothing
   notUserStep this = this

keyToProofStep :: Key -> Maybe ProofStep
keyToProofStep key = 
   case readM key of
      Just c                       -> Just (InductiveStep c)
      _ | key `elem` knownMetaVars -> Just (IHStep key)
        | key `elem` knownAtoms    -> Just (BaseStep key)
        | not (null key)           -> Just (UserStep key Nothing)
        | otherwise                -> Nothing

metavarProofs :: Inductive -> [(MetaVar, RelProof)]
metavarProofs = concatMap f . proofs
 where
   f (Just (IHStep s), rp) = [(s, rp)]
   f _ = []

inductiveStepProofs :: Inductive -> [(Int, (Maybe ProofStep, RelProof))]
inductiveStepProofs = filter (isInductiveStep . fst . snd) . f
 where
    f ind =  [ (i, prf) | (i, prf) <- zip [0..] (proofs ind) ]

    isInductiveStep (Just (InductiveStep _)) = True
    isInductiveStep _ = False

ihStepProofs :: Inductive -> [(Int, (Maybe ProofStep, RelProof))]
ihStepProofs = filter (isIHStep . fst . snd) . f
 where
   f ind = [ (i, prf) | (i, prf) <- zip [0..] (proofs ind) ]
   
   isIHStep (Just (IHStep _)) = True
   isIHStep _ = False

knownAtoms :: [String]
knownAtoms = ["p", "q", "r"]

knownMetaVars :: [MetaVar]
knownMetaVars = ["phi", "psi", "chi"]

knownCases :: [Case]
knownCases = [NEGATION, AND, OR, IMPLIES]

knownProofSteps :: [ProofStep]
knownProofSteps = map BaseStep knownAtoms ++ map IHStep knownMetaVars ++ map InductiveStep knownCases

-- infer case for all proofs (ignoring provided cases)
-- if exactly one case is inferred, and there currently is no active case, set this inferred case as active
inferCases :: Inductive -> Inductive
inferCases ind = ind { proofs = newProofs, active = newActive }
 where
   newProofs = map f (proofs ind)
   newActive = 
      case catMaybes $ zipWith g (proofs ind) newProofs of
         [ps] | isNothing (active ind) -> Just ps
         _ -> active ind

   f (original, rp) = checkUserStep original $
      case matchLhs (theorem (initial ind)) (topExpr rp) of
         Just ([(_, TVar s)], _) 
            | s  `elem` knownAtoms    -> (Just (BaseStep s), rp)
            | s  `elem` knownMetaVars -> (Just (IHStep s), setMotivationIH rp)
         Just ([(_, TCon sym args)], _)
              -- first check that the operands of the logic operator are all meta variables
            | any notMetaVar args        -> (Nothing, rp)
            | not (allAreDifferent args) -> (Nothing, rp)
            | sym == Logic.andSymbol     -> (Just (InductiveStep AND), rp)
            | sym == Logic.orSymbol      -> (Just (InductiveStep OR), rp)
            | sym == Logic.impliesSymbol -> (Just (InductiveStep IMPLIES), rp)
            | sym == Logic.notSymbol     -> (Just (InductiveStep NEGATION), rp)
         _ -> (Nothing, rp)

   notMetaVar = (`notElem` map TVar knownMetaVars)
   
   allAreDifferent []     = True
   allAreDifferent (x:xs) = x `notElem` xs && allAreDifferent xs

   g (Nothing, _) (Just ps, _) = Just ps
   g (Just (UserStep _ _), _) (Just ps, _) = Just ps
   g _ _ = Nothing

-- checks that the step provided by the user (one of the three categories) matches the inferred case. If so, 
-- ignore user category. In case there is no match, combine the user step with the inferred case.
checkUserStep :: Show a => Maybe ProofStep -> (Maybe ProofStep, a) -> (Maybe ProofStep, a)
checkUserStep (Just (UserStep "basestep" _)) pair@(Just (BaseStep _), _) = pair
checkUserStep (Just (UserStep "ihstep" _)) pair@(Just (IHStep _), _) = pair
checkUserStep (Just (UserStep "inductivestep" _)) pair@(Just (InductiveStep _), _) = pair
checkUserStep (Just (UserStep s _)) (mps, a) = (Just (UserStep s mps), a)
checkUserStep _ pair = pair

-- set motivation to 'ih' (only for IHStep)
setMotivationIH :: RelProof -> RelProof
setMotivationIH rp = fromMaybe rp $ close "ih" rp

proofForStep :: ProofStep -> Theorem -> [MetaVar] -> Maybe RelProof
proofForStep ps th mvs = ihClose ps . relationToProof . (`instantiate` th) <$> rec ps
 where
   rec (BaseStep s)             = return (Var s)
   rec (IHStep mv)              = return (Var mv)
   rec (InductiveStep AND)      = binop (<&&>) mvs
   rec (InductiveStep OR)       = binop (<||>) mvs
   rec (InductiveStep IMPLIES)  = binop (<->>) mvs
   rec (InductiveStep NEGATION) = unop complement mvs
   rec (UserStep _ ms)          = maybe (fail "user step") rec ms

   ihClose (IHStep _) rp = fromMaybe rp $ close "ih" rp
   ihClose _          rp = rp
   
   binop op (x:y:_) = return $ op (Var x) (Var y)
   binop _ _        = fail "insufficient metavars for proofForStep"

   unop op (x:_) = return $ op (Var x)
   unop _ _      = fail "insufficient metavars for proofForStep"
   
replaceVar :: (String -> Expr) -> Expr -> Expr
replaceVar f = rec 
 where
   rec (Var s) = f s
   rec x = descend rec x

------------------------------------------------------------------------------
-- Initial

data Initial = Initial
   { problem     :: Problem
   , language    :: Language
   , definitions :: [Id]
   , motivations :: [Id]
   , theorem     :: Theorem
     -- and special definitions
   }
 deriving (Show, Eq)

newtype Problem = Dictionary [(ProblemLanguage, String)]
   deriving Eq

instance Show Problem where
   show (Dictionary xs) = show xs

data ProblemLanguage = NL | EN 
   deriving (Show, Read, Eq)

instance InJSON Initial where
   toJSON = Object . initialObject
   jsonDecoder = Initial 
      <$> jKey "problem" jsonDecoder
      <*> jKey "language" languageDecoder
      <*> (jKey "definitions" definitionsDecoder <|> pure [])
      <*> (jKey "motivations" motivationsDecoder <|> pure [])
      <*> jKey "theorem" theoremDecoder

instance InJSON Problem where
   toJSON (Dictionary xs) = Object $ map (\(pl, s) -> (map toLower (show pl), toJSON s)) xs
   jsonDecoder = Dictionary . mapMaybe f <$> jObjectWithKeys dec
    where
      dec k = (,) (readM (map toUpper k)) <$> jString

      f (Just a, b)  = Just (a, b)
      f (Nothing, _) = Nothing

instance IsTerm Initial where
   toTerm (Initial txt xs defs mots th) = toTerm (txt, xs, (defs, mots, th))
   termDecoder = (\(txt, xs, (defs, mots, th)) -> Initial txt xs defs mots th) <$> termDecoder

instance IsTerm Problem where
   toTerm (Dictionary xs) = toTerm xs
   termDecoder = Dictionary <$> termDecoder

instance IsTerm ProblemLanguage where
   toTerm = toTerm . show
   termDecoder = fromMaybe EN . readM <$> termDecoder

initialObject :: Initial -> [(Key, JSON)]
initialObject st = 
   [ ("problem", toJSON $ problem st)
   , ("language", languageToJSON $ language st)
   , ("definitions", Array $ map (toJSON . show) $ definitions st)
   , ("motivations", Array $ map (toJSON . show) $ motivations st)
   , ("theorem", theoremToJSON $ theorem st)
   ] 
   
definitionsDecoder :: DecoderJSON [Id]
definitionsDecoder = jArrayOf (newId <$> jString)

motivationsDecoder :: DecoderJSON [Id]
motivationsDecoder = jArrayOf (newId <$> jString)

definitionsFromJSON :: JSON -> Maybe [Id]
definitionsFromJSON (Array xs) = mapM f xs
 where
   f (String s) = Just (newId s)
   f _ = Nothing
definitionsFromJSON _ = Nothing
   
------------------------------------------------------------------------------
-- Rest

fromElement :: Element -> ProofStep
fromElement = either fromAtom InductiveStep

fromAtom :: SpecialAtom -> ProofStep
fromAtom = BaseStep

fromCase :: Case -> ProofStep
fromCase = InductiveStep

preferredVarAtom :: Language -> VarAtom
preferredVarAtom l = head $ filter (`notElem` specialAtoms l) knownAtoms

specialAtoms :: Language -> [SpecialAtom]
specialAtoms = lefts

type Language    = [Element]
type Element     = Either SpecialAtom Case
type SpecialAtom = String -- hoe negaties van atomen mee te nemen?
type VarAtom     = String
type MetaVar     = String -- phi, psi, chi

data Case = NEGATION | AND | OR | IMPLIES 
 deriving (Show, Read, Eq, Ord)
 
instance IsId Case where
   newId = newId . show

instance IsTerm Case where
   toTerm AND      = symbol andSymbol
   toTerm OR       = symbol orSymbol
   toTerm IMPLIES  = symbol impliesSymbol
   toTerm NEGATION = symbol negationSymbol
   
   termDecoder 
      =  AND      <$ tCon0 andSymbol
     <|> OR       <$ tCon0 orSymbol
     <|> IMPLIES  <$ tCon0 impliesSymbol
     <|> NEGATION <$ tCon0 negationSymbol

connarity :: ProofStep -> Int  
connarity  (InductiveStep NEGATION) = 1
connarity (InductiveStep AND) = 2
connarity (InductiveStep IMPLIES) = 2
connarity(InductiveStep OR) = 2
connarity _ = -1

languageDecoder :: DecoderJSON Language
languageDecoder = jArrayOf ((\s -> maybe (Left s) Right $ readM s) <$> jString)

languageToJSON :: Language -> JSON
languageToJSON xs = Array [ String $ either id show x | x <- xs ]

andSymbol, orSymbol, impliesSymbol, negationSymbol :: Symbol
andSymbol      = newSymbol "inductive.and"
orSymbol       = newSymbol "inductive.or"
impliesSymbol  = newSymbol "inductive.implies"
negationSymbol = newSymbol "inductive.negation"