{-# LANGUAGE RankNTypes #-}
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
-----------------------------------------------------------------------------

module Domain.Logic.Equivalence.SplitProof 
   ( SplitProof, showAsSplitProof
   , partRef
   , liftPair
   , stepPairDir
   , stepPart
   , stepTD, stepBU, somePart
   , acTopRuleFor
   , sw -- to do: hide me
   ) where

import Control.Monad
import Data.Char
import Data.Either
import Data.Foldable
import Data.List
import Data.Maybe
import Domain.Logic.Formula
import Domain.Logic.Equivalence.Data
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.Relation
import Domain.Logic.Utils
import Ideas.Common.Library
import Ideas.Utils.Uniplate
import Ideas.Utils.Prelude

data SplitProof = SP 
   { splitProof  :: Logic (Either (SLogic, SLogic) ShowString) 
   , onDirection :: Direction
   , onPart      :: Int
   }

getParts :: SplitProof -> [(SLogic, SLogic)]
getParts = lefts . toList . splitProof

showAsSplitProof :: Proof -> String
showAsSplitProof prf = 
   case isOpen prf of
      Nothing -> "ok"
      Just (p, is, q) -> 
         let sp = toSplitProof (makeEnvironment []) (p, q)
             sh f = show (fmap (either (ShowString . brackets . show . f) id) (splitProof sp))
             brackets s = "[" ++ s ++ "]"
         in sh fst ++ "  " ++ show is ++ "  " ++ sh snd

toSplitProof :: HasEnvironment a => a -> (SLogic, SLogic) -> SplitProof
toSplitProof env pair = SP (rec pair) (fromMaybe TopDown $ directionRef ? env) (fromMaybe 0 $ partRef ? env)
 where 
   rec (p, q) = 
      case (p, q) of
         (_ :&&: _, _ :&&: _) -> 
            case acSplitFor False (collect andView) (p, q) of
               [] -> Var (Left (p, q))
               (p1, p2, q1, q2):_ -> 
                  rec (p1, q1) :&&: rec (p2, q2)
         (_ :||: _, _ :||: _) -> 
            case acSplitFor False (collect orView) (p, q) of
               [] -> Var (Left (p, q))
               (p1, p2, q1, q2):_ -> 
                  rec (p1, q1) :||: rec (p2, q2)
         (p1 :<->: p2,  q1 :<->: q2) | eqLogic p1 q1 && eqLogic p2 q2 ->
            rec (p1, q1) :<->: rec (p2, q2)
         (p1 :->: p2,  q1 :->: q2) | eqLogic p1 q1 && eqLogic p2 q2 ->
            rec (p1, q1) :->: rec (p2, q2)
         (Not p1, Not q1) | eqLogic p1 q1 ->
            Not (rec (p1, q1))
         (Var x, Var y) | x == y -> Var (Right x)
         (T, T) -> T
         (F, F) -> F
         _ -> Var (Left (p, q))

fromSplitProof :: SplitProof -> (SLogic, SLogic)
fromSplitProof (SP p _ _) = (catLogic (make fst p), catLogic (make snd p))
 where
   make f = fmap (either f Var)

partRef :: Ref Int
partRef = makeRef "part"

replaceItem :: Int -> b -> [Either b c] -> [Either b c]
replaceItem _ _ []             = []
replaceItem 0 p (Left _:rest)  = Left p:rest
replaceItem n p (Right x:rest) = Right x:replaceItem n p rest
replaceItem n p (Left x:rest)  = Left x:replaceItem (n-1) p rest

replaceVars :: [b] -> Logic a -> Logic b
replaceVars bs = fst . rec bs
 where
   rec xs T           = (T, xs)
   rec xs F           = (F, xs)
   rec xs (Not p)     = first Not (rec xs p)
   rec xs (p :&&: q)  = bin xs (:&&:) p q
   rec xs (p :||: q)  = bin xs (:||:) p q
   rec xs (p :->: q)  = bin xs (:->:) p q
   rec xs (p :<->: q) = bin xs (:<->:) p q
   rec (x:xs) (Var _) = (Var x, xs)
   rec [] (Var _)     = error "replaceVars: empty list"

   bin xs f p q =
      let (np, ys) = rec xs p
          (nq, zs) = rec ys q
      in (f np nq, zs)

lift4 :: Lift f => f SLogic -> f (Environment, (SLogic, SLogic))
lift4 = liftWith f 
 where
   f (env, (x, y))
      | dir == TopDown = (x, \nx -> (env, (nx, y)))
      | otherwise      = (y, \ny -> (env, (x, ny)))
    where
      dir = fromMaybe TopDown (directionRef ? env)

liftPair :: Lift f => f (SLogic, SLogic) -> f (Context Proof)
liftPair s = lift0123 (maf s)
 where
   maf :: Lift f => f (SLogic, SLogic) -> f (Environment, (SLogic, SLogic))
   maf = liftWith $ \(env, pair) -> (pair, \new -> (env, new))

lift0123 :: Lift f => f (Environment, (SLogic, SLogic)) -> f (Context Proof)
lift0123 = f0 . f1 . f2 . f3 . f4
 where 
   f0 :: Lift f => f (Environment, a) -> f (Context a)
   f0 = liftWithM $ \ctx -> do
      a <- fromContext ctx
      let back (nenv, b) = setEnvironment nenv (replaceInContext b ctx)
      return ((environment ctx, a), back)

   f1 :: Lift f => f (Environment, (SLogic, SLogic)) -> f (Environment, Proof)
   f1 = liftWithM $ \(env, p) -> do
      (x, rp, y) <- isOpen p
      let back (nx, ny) = fromJust $ replaceMiddle (nx, rp, ny) p
      return ((env, (x, y)), second back)

   f2 :: Lift f => f (Environment, SplitProof) -> f (Environment, (SLogic, SLogic))
   f2 = liftWith $ \(env, x) -> 
      ((env, toSplitProof env x), \(nenv, sp) -> (nenv, fromSplitProof sp)) -- !! terugschrijven

   f3 :: Lift f => f (Environment, (SLogic, SLogic)) -> f (Environment, SplitProof)
   f3 = liftWithM $ \(env, SP p od op) ->
      let n = fromMaybe 0 (partRef ? env)
          pairs = toList p
      in case drop n (lefts pairs) of
            []  -> Nothing
            y:_ -> Just ((env, y), fmap $ \ny -> SP (replaceVars (replaceItem n ny pairs) p) od op)

   f4 :: Lift f => f (Environment, (SLogic, SLogic)) -> f (Environment, (SLogic, SLogic))
   f4 = liftWith $ \(env, pair) -> 
      let (newPair, sub) = findAtomicParts pair 
      in ((env, newPair), \(env', p') -> (env', restoreAtomicParts sub p'))

type Substitution = [(Int, SLogic)]

findAtomicParts :: (SLogic, SLogic) -> ((SLogic, SLogic), Substitution)
findAtomicParts (p, q) = 
   ((sub <-| p, sub <-| q), sub) -- if null sub then [] else error $ show (sub, (sub <-| p, sub <-| q)))
 where
   xs  = filter (\x -> checkForm x && checkEq x) (universe p `intersect` universe q)
   sub = zip [0..] xs 

   -- also exclude not-formula because this interferes with the normalization procedure
   checkForm (Var _) = False
   checkForm (Not _) = False
   checkForm _       = True 

   checkEq r = f p `eqLogic` f q
    where -- note: niet per se alle voorkomens, maar tenminste 1 (betere oplossing?)
      f a = [(0, r)] <-| a

-- reverse substitution
(<-|) :: Substitution -> SLogic -> SLogic
sub <-| a = 
   case filter ((== a) . snd) sub of
      [(i, _)] -> Var (ShowString $ show i)
      _ -> descend (sub <-|) a 

(|->) :: Substitution -> SLogic -> SLogic
sub |-> (Var (ShowString s)) | all isDigit s = 
   fromJust (lookup (read s) sub)
sub |-> a = descend (sub |->) a

restoreAtomicParts :: Substitution -> (SLogic, SLogic) -> (SLogic, SLogic)
restoreAtomicParts sub (p, q) = (sub |-> p, sub |-> q)

newLift :: Lift f => f SplitProof -> f (Context Proof)
newLift = liftWithM $ \ctx -> do
   prf <- fromContext ctx
   (lhs, rp, rhs) <- isOpen prf
   let sp = toSplitProof ctx (lhs, rhs)
   return (sp, \nsp -> let (newLhs, newRhs) = fromSplitProof nsp
                       in insertRef partRef (onPart nsp) $ insertRef directionRef (onDirection nsp) $ replaceInContext (fromJust $ replaceMiddle (newLhs, rp, newRhs) prf) ctx)

-- the result needs to be a rule (instead of a strategy), such that the resulting rule (including the step in the proof)
-- can be recognized by the domain reasoner. Also copy sibling information (also other info???)
stepPart :: Rule SLogic -> Rule (Context Proof)
stepPart r = siblingsOf (ruleSiblings r) $ (if isBuggy r then buggy else id) $
   makeRule (getId r) $ applyAll (somePart (step r))

-- to do: move this function to the ideas library
siblingsOf :: HasId b => [b] -> Rule a -> Rule a
siblingsOf xs r = foldr siblingOf r xs

step :: Rule SLogic -> Strategy (Context Proof)
step r = stepTD (showId r) .*. lift0123 (lift4 (sw r))
       .|. stepBU (showId r) .*. lift0123 (lift4 (sw r))

stepPairDir :: (Direction -> Rule (SLogic, SLogic)) -> Strategy (Context Proof)
stepPairDir f = stepTD (showId r1) .*. lift0123 (liftWith (\(env, p) -> (p, \q -> (env, q))) r1)
            .|. stepBU (showId r2) .*. lift0123 (liftWith (\(env, p) -> (p, \q -> (env, q))) r2)
 where
   r1 = f TopDown
   r2 = f BottomUp

somePart :: IsStrategy f => f (Context Proof) -> Strategy (Context Proof)
somePart a = newLift resetPart .*. newLift (many incrPart) .*. a

resetPart :: Rule SplitProof
resetPart = minorRule "resetPart" $ \sp ->
   Just sp { onPart = 0 }

incrPart :: Rule SplitProof
incrPart = minorRule "incrPart" $ \sp -> do
   let next = onPart sp + 1
   guard $ next < length (getParts sp)
   Just sp { onPart = next }

stepTD :: Motivation -> Rule (Context Proof)
stepTD m = minorRule "stepTD" $ \ctx -> do 
   prf <- fromContext ctx
   (p, _, _) <- isOpen prf
   new <- extendUpper (Equal, m) p prf
   return $ replaceInContext new (insertRef directionRef TopDown ctx)

stepBU :: Motivation -> Rule (Context Proof)
stepBU m = minorRule "stepBU" $ \ctx -> do 
   prf <- fromContext ctx
   (_, _, p) <- isOpen prf
   new <- extendLower (Equal, m) p prf
   return $ replaceInContext new (insertRef directionRef BottomUp ctx)

sw :: Rule SLogic -> Rule SLogic
sw r = makeRule (getId r) rec
 where
   rec p = [ f q' | (q, f) <- contexts p, q' <- applyAll r q ]

-------------------------------

acSplitFor :: Eq a => Bool -> (forall b . Isomorphism (Logic b) [Logic b])
             -> (Logic a, Logic a) -> [(Logic a, Logic a, Logic a, Logic a)]
acSplitFor com iso (lhs, rhs) = do
   let as = from iso lhs
       bs = from iso rhs
       splitter = if com then divide else split
   (as1, as2, bs1, bs2) <- splitTwoLists splitter as bs
   let eqList xs ys = eqLogic (to iso xs) (to iso ys)
       f = to iso
   guard (eqList as1 bs1 && eqList as2 bs2)
   return (f as1, f as2, f bs1, f bs2)

acTopRuleFor :: Eq a => Bool -> (forall b . Isomorphism (Logic b) [Logic b])
             -> (Logic a, Logic a) -> [(Logic a, Logic a)]
acTopRuleFor com iso pair@(lhs, rhs) = do
   (a1, a2, b1, b2) <- acSplitFor com iso pair
   let newLhs = to iso [a1, a2]
       newRhs = to iso [b1, b2]
   return $
      -- if both sides have changed ...
      if newLhs /= lhs && newRhs /= rhs
      then -- ... only keep the reordering on the left-hand side
         (newLhs, rhs)
      else -- ... otherwise, decompose proof with "top" rule
         ( newLhs
         , newRhs
         )

splitTwoLists :: (forall t . [t] -> [([t], [t])])
              -> [a] -> [b] -> [([a], [a], [b], [b])]
splitTwoLists f as bs =
   [ (as1, as2, bs1, bs2)
   | (as1, as2) <- f as
   , not (null as1 || null as2)
   , (bs1, bs2) <- f bs
   , not (null bs1 || null bs2)
   ]

divide :: [a] -> [([a], [a])] -- associative + commutative
divide = foldr op [([], [])]
 where
   op a xs = map addLeft xs ++ map addRight xs
    where
      addLeft  (ys, zs) = (a:ys, zs)
      addRight (ys, zs) = (ys, a:zs)