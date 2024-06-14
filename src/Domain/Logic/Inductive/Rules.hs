module Domain.Logic.Inductive.Rules 
   ( inductionHypothesis, inductionHypothesisClose
   , startNewInductiveCase, startNewBaseCase, startNewSubProof
   , showBaseCases, showInductiveCases, showIH
   ) where

import Control.Monad
import Data.Either (rights)
import Data.Maybe
import Data.List (sort, (\\), partition)
import Domain.Logic.Inductive.Theorem
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.RelProof
import Domain.Logic.Inductive.RP
import Ideas.Common.Library

inductionHypothesis :: Rule (RelProof, Initial)
inductionHypothesis = makeRule "ih" $ \(rp, inl) -> do
   new <- applyIH rp (theorem inl)
   return (new, inl)

inductionHypothesisClose :: Rule (RelProof, Initial)
inductionHypothesisClose = makeRule "ih.close" $ \(rp, inl) -> do
   new    <- applyIH rp (theorem inl)
   closed <- closeEqual False new -- when merging, keep the lower term in the middle
   return (closed, inl)

startNewSubProofWith :: Inductive -> ProofStep -> Maybe Inductive
startNewSubProofWith a el = do 
   rp <- proofForStep el th mvs
   return $ setActive (Just el) $ a { proofs = cs ++ [(Just el, rp)] }
 where cs      = proofs a
       ini     = initial a
       th      = theorem ini
       mvs     = map fst (metavarProofs a)
   
startNewSubProof :: Rule Inductive
startNewSubProof = makeRule "new-subproof" $ \a -> do
   let cs      = proofs a
       ini     = initial a
       present = mapMaybe fst cs
       hasVarAtom = any (isVarAtomStep (language ini) . fst) cs
       (ihs1, ihs2) = partition (`elem` present) ihsteps
       missing = take (2 - length ihs1) ihs2 ++
                 (map fromElement (language ini) \\ present) ++
                 [ BaseStep (preferredVarAtom (language ini))
                 | not hasVarAtom
                 ]
   ps <- listToMaybe (sort missing)
   startNewSubProofWith a ps

startNewBaseCase :: Rule Inductive
startNewBaseCase = minorRule "new-basecase" $ \a -> do
   let cs      = [(step, prf)|
                   (step, prf) <- proofs a,
                    readyRelProof th prf]
       ini     = initial a
       th      = theorem ini
       bcs     = specialAtoms $ language ini
       present = mapMaybe fst cs
       hasVarAtom = any (isVarAtomStep (language ini) . fst) cs

       missing = (sort (map fromAtom bcs) \\ present) ++
                 [ BaseStep (preferredVarAtom (language ini))
                 | not hasVarAtom
                 ]

   ps <- listToMaybe missing
   guard (active a /= Just ps)
   return $ setActive (Just ps) a

startNewInductiveCase :: Rule Inductive
startNewInductiveCase = minorRule "new-inductivecase" $ \a -> do
   let cs      = [(step, prf)|
                   (step, prf) <- proofs a,
                    readyRelProof th prf]
       ini     = initial a
       th      = theorem ini
       ics     = rights $ language ini
       present = mapMaybe fst cs
       missing = sort (map fromCase ics) \\ present
   -- the active subproof is not open
   guard $ case active a of
      Just act -> maybe False (isNothing . isOpen) (Just act `lookup` proofs a)
      Nothing  -> True
   -- the active subproof is not in the set of missing subproofs
   guard $ maybe True (`notElem` missing) (active a)
   ps <- missing
   return $ setActive (Just ps) a

showBaseCases :: Rule Inductive
showBaseCases = makeRule "basecases" $ \a -> do
   let cs  = proofs a
       ini = initial a
       th  = theorem ini
   new <- sequence $ 
             [ proofFor (Left at) th knownMetaVars >>= \rp -> return (Just (fromAtom at), rp) 
             | at <- specialAtoms (language ini) 
             , Just (fromAtom at) `notElem` map fst (proofs a)
             ] ++
             [ proofForStep st th knownMetaVars >>= \rp -> return (Just st, rp)
             | let st = BaseStep (preferredVarAtom (language ini))
             , not (any (isVarAtomStep (language ini) . fst) cs)
             ]
   guard (not (null new))
   Just $ setActive (fst (head new)) a { proofs = new ++ proofs a }
 
showIH :: Rule Inductive
showIH = makeRule "hypotheses" $ \a -> do
   let cs      = proofs a
       ini     = initial a
       th      = theorem ini
       (ihs1, ihs2) = partition ((`elem` map fst cs) . Just) ihsteps
   guard (length ihs1 < 2)
   new <- mapM (\x -> proofForStep x th knownMetaVars) (take (2 - length ihs1) ihs2)
   Just $ setActive Nothing a { proofs = cs ++ zip (map Just ihs2) new }

showInductiveCases :: Rule Inductive
showInductiveCases = makeRule "inductivecases" $ \a -> do
   let cs      = proofs a
       ini     = initial a
       elts    = language ini
       ics     = [ e | c <- rights elts, let e = fromCase c, Just e `notElem` map fst cs ]
       mvs     = map fst (metavarProofs a)
   guard (not (null ics))
   bsct <- sequence [ proofForStep el (theorem ini) mvs | el <- ics ]
   Just a {  proofs = cs ++ zip (map Just ics) bsct }

----------------------------

isVarAtomStep :: Language -> Maybe ProofStep -> Bool
isVarAtomStep l (Just (BaseStep s)) = s `notElem` specialAtoms l
isVarAtomStep _ _ = False

ihsteps :: [ProofStep] -- to do: determine number of meta vars
ihsteps = map IHStep knownMetaVars

proofFor :: Element -> Theorem -> [MetaVar] -> Maybe RelProof
proofFor el = proofForStep (fromElement el)