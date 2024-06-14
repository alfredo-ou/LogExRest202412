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
-- Generalized rules, and inverse rules, for De Morgan and distributivity
--
-----------------------------------------------------------------------------

module Domain.Logic.GeneralizedRules
   ( generalAssoc, generalComm, generalRuleDeMorganOr, generalRuleDeMorganAnd
   , generalRuleDistrAnd, generalRuleDistrOr
   , generalRuleInvDoubleNegAnd, generalRuleInvDoubleNegOr
   , absorptionOrSubsetCom, absorptionOrSubsetSort
   , absorptionAndSubsetCom, absorptionAndSubsetSort
   ) where

-- Note: the generalized rules do not take AC-unification into account,
-- and perhaps they should.
import Control.Monad
import Data.Function
import Data.List
import Domain.Logic.Formula
import Domain.Logic.Generator (equalLogicA, equalLogicAC)
import Domain.Logic.Utils
import Ideas.Common.Library
import Ideas.Utils.Prelude (split3, split4, isSubsetOf, distinct)
import Data.Maybe

-----------------------------------------------------------------------------
-- Generalized rules

-- associativity, possibly multiple: only recognizer
generalAssoc :: Rule (Context SLogic)
generalAssoc = setMinor True $ siblingOf groupAssociativity $ makeRecognizerRule "assoc" $ \x y ->
   x /= y && equalLogicA x y

-- commutativity, possibly multiple: only recognizer
generalComm :: Rule (Context SLogic)
generalComm = siblingOf groupCommutativity $ makeRecognizerRule "comm" $ \x y ->
   equalLogicAC x y && not (equalLogicA x y)

generalRuleDeMorganOr :: Rule SLogic
generalRuleDeMorganOr =
   siblingOf groupDeMorgan $ makeListRule "GenDeMorganOr" f
 where
   f (Not e) = do
      xs <- subDisjunctions e
      guard (length xs > 2)
      return (ands (map Not xs))
   f _ = []

generalRuleDeMorganAnd :: Rule SLogic
generalRuleDeMorganAnd =
   siblingOf groupDeMorgan $ makeListRule "GenDeMorganAnd" f
 where
   f (Not e) = do
      xs <- subConjunctions e
      guard (length xs > 2)
      return (ors (map Not xs))
   f _ = []

generalRuleDistrAnd :: Rule SLogic
generalRuleDistrAnd =
   siblingOf groupDistribution $ makeListRule "GenAndOverOr" f
 where
   f p = do -- left distributive
      (leftCtx, x, y, rightCtx) <- getConjunctionTop4 p 
      ys <- subDisjunctions y
      guard (length ys > 2)
      return (ands (leftCtx ++ [ors (map (x :&&:) ys)] ++ rightCtx))
    `mplus` do -- right distributive
      (leftCtx, x, y, rightCtx) <- getConjunctionTop4 p 
      xs <- subDisjunctions x
      guard (length xs > 2)
      return (ands (leftCtx ++ [ors (map (:&&: y) xs)] ++ rightCtx))

generalRuleDistrOr :: Rule SLogic
generalRuleDistrOr =
   siblingOf groupDistribution $ makeListRule "GenOrOverAnd" f
 where
   f p = do -- left distributive
      (leftCtx, x, y, rightCtx) <- getDisjunctionTop4 p
      ys <- subConjunctions y
      guard (length ys > 2)
      return (ors (leftCtx ++ [ands (map (x :||:) ys)] ++ rightCtx))
    `mplus` do -- right distributive
       (leftCtx, x, y, rightCtx) <- getDisjunctionTop4 p
       xs <- subConjunctions x
       guard (length xs > 2)
       return (ors (leftCtx ++ [ands (map (:||: y) xs)] ++ rightCtx))

generalRuleInvDoubleNegAnd :: Rule SLogic
generalRuleInvDoubleNegAnd =
   siblingOf groupDoubleNegation $ makeListRule "GenInvDoubleNegAnd" f
 where
   f p = do 
      (leftCtx, x, rightCtx) <- getConjunctionTop3 p
      guard (not (null leftCtx && null rightCtx))
      return (ands (leftCtx ++ [Not (Not x)] ++ rightCtx)) 

generalRuleInvDoubleNegOr :: Rule SLogic
generalRuleInvDoubleNegOr =
   siblingOf groupDoubleNegation $ makeListRule "GenInvDoubleNegOr" f
 where
   f p = do 
      (leftCtx, x, rightCtx) <- getDisjunctionTop3 p
      guard (not (null leftCtx && null rightCtx))
      return (ors (leftCtx ++ [Not (Not x)] ++ rightCtx)) 

{-
absorptionOrSubset :: Rule SLogic
absorptionOrSubset = siblingOf groupAbsorption $ ruleList "absorpor-subset" $ \p -> do
   let xss = map conjunctions (disjunctions p)
       yss = filter (\xs -> all (ok xs) xss) xss
       ok xs ys = not (ys `isSubsetOf` xs) || xs == ys || length xs < 2
   -- error $ show (length xss, length yss, map show xss, map show yss)
   guard (length yss < length xss)
   return $ ors (map ands yss) -}

-- zoek naar twee rijtjes van conjuncten waarvan de één een subset is van de ander, en plaats die 
-- naast elkaar (onder de voorwaarde dat ze nog niet naast elkaar stonden)
absorptionOrSubsetCom :: Rule SLogic
absorptionOrSubsetCom = siblingOf groupCommutativity $ makeListRule "absorpor-subset-com" $ \p -> do
   let xss = map conjunctions (disjunctions p)
       pairs = [ (i, j, ys) | (i, xs) <- zip [0..] xss, (j, ys) <- zip [0..] xss, xs `isSubsetOf` ys, xs /= ys ]
   guard $ all (\(i, j, _) -> abs (i-j) > 1) pairs
   (i, j, ys) <- pairs
   let (as, b:bs) = splitAt i xss
   let reordered | j < i     = deleteAt j as ++ b : ys : bs
                 | otherwise = as ++ b : ys : deleteAt (j-i-1) bs
   return $ ors (map ands reordered)

-- er staan twee rijtjes van conjuncten naast elkaar waarop een absorptie mogelijk is. Sorteer nu 
-- eerst het langere rijtje zoals het kortere. Voordat je dit doet eerst dubbelen weggooien met 
-- idempotentie
absorptionOrSubsetSort :: Rule SLogic
absorptionOrSubsetSort = siblingOf groupCommutativity $ makeListRule "absorpor-subset-sort" $ \p -> do
   let xss = map conjunctions (disjunctions p)
   (j, xs, ys) <- [ (j, xs, ys) | (i, xs) <- zip [0..] xss, (j, ys) <- zip [0..] xss
                  , xs `isSubsetOf` ys, xs /= ys, abs (i-j) == 1, distinct xs, distinct ys ]
   let (as, _:bs) = splitAt j xss
       ys2 = filter (`notElem` xs) ys
       reordered  = as ++ (xs ++ ys2) : bs
   guard $ (xs ++ ys2) /= ys && (ys2 ++ xs) /= ys
   return $ ors (map ands reordered)

-- zoek naar twee rijtjes van disjuncten waarvan de één een subset is van de ander, en plaats die 
-- naast elkaar (onder de voorwaarde dat ze nog niet naast elkaar stonden)
absorptionAndSubsetCom :: Rule SLogic
absorptionAndSubsetCom = siblingOf groupCommutativity $ makeListRule "absorpand-subset-com" $ \p -> do
   let xss = map disjunctions (conjunctions p)
       pairs = [ (i, j, ys) | (i, xs) <- zip [0..] xss, (j, ys) <- zip [0..] xss, xs `isSubsetOf` ys, xs /= ys ]
   guard $ all (\(i, j, _) -> abs (i-j) > 1) pairs
   (i, j, ys) <- pairs
   let (as, b:bs) = splitAt i xss
   let reordered | j < i     = deleteAt j as ++ b : ys : bs
                 | otherwise = as ++ b : ys : deleteAt (j-i-1) bs
   return $ ands (map ors reordered)

-- er staan twee rijtjes van disjuncten naast elkaar waarop een absorptie mogelijk is. Sorteer nu 
-- eerst het langere rijtje zoals het kortere. Voordat je dit doet eerst dubbelen weggooien met 
-- idempotentie
absorptionAndSubsetSort :: Rule SLogic
absorptionAndSubsetSort = siblingOf groupCommutativity $ makeListRule "absorpand-subset-sort" $ \p -> do
   let xss = map disjunctions (conjunctions p)
   (j, xs, ys) <- [ (j, xs, ys) | (i, xs) <- zip [0..] xss, (j, ys) <- zip [0..] xss
                  , xs `isSubsetOf` ys, xs /= ys, abs (i-j) == 1, distinct xs, distinct ys ]
   let (as, _:bs) = splitAt j xss
       ys2 = filter (`notElem` xs) ys
       reordered  = as ++ (xs ++ ys2) : bs
   guard $ (xs ++ ys2) /= ys && (ys2 ++ xs) /= ys
   return $ ands (map ors reordered)

deleteAt :: Int -> [a] -> [a]
deleteAt i xs = let (xs1, xs2) = splitAt i xs in xs1 ++ drop 1 xs2

-------------------------------------------------------------------------
-- Helper functions

-- warning: do not lift such a recognizer rule
makeRecognizerRule :: String -> (SLogic -> SLogic -> Bool) -> Rule (Context SLogic)
makeRecognizerRule n f = addRecognizerBool eqc $ makeSimpleRule n (const Nothing)
 where
   eqc cx cy = fromMaybe False $ do
      f <$> fromContext cx <*> fromContext cy

getDisjunctionTop3 :: SLogic -> [([SLogic], SLogic, [SLogic])]
getDisjunctionTop3 = mapMaybe f . split3 . disjunctions
 where
   f (x, y, z)
      | length y > 1 = Just (x, ors y, z)
      | otherwise    = Nothing

getConjunctionTop3 :: SLogic -> [([SLogic], SLogic, [SLogic])]
getConjunctionTop3 = mapMaybe f . split3 . conjunctions
 where
   f (x, y, z) 
      | length y > 1 = Just (x, ands y, z)
      | otherwise    = Nothing

getDisjunctionTop4 :: SLogic -> [([SLogic], SLogic, SLogic, [SLogic])]
getDisjunctionTop4 = sortSmallContext . mapMaybe f . split4 . disjunctions
 where
   f (x, y, z, u) 
      | not (null y || null z) = Just (x, ors y, ors z, u)
      | otherwise = Nothing

getConjunctionTop4 :: SLogic -> [([SLogic], SLogic, SLogic, [SLogic])]
getConjunctionTop4 = sortSmallContext . mapMaybe f . split4 . conjunctions
 where
   f (x, y, z, u)
      | not (null y || null z) = Just (x, ands y, ands z, u)
      | otherwise = Nothing

-- This order tries to use as many elements as possible as distribuant
-- (small/empty left and right contexts are preferable)
sortSmallContext :: [([a], a, a, [a])] -> [([a], a, a, [a])]
sortSmallContext = sortBy (compare `on` f)
 where
   f (xs, _, _, ys) = length xs + length ys

-- All combinations where some disjunctions are grouped, and others are not
subDisjunctions :: SLogic -> [[SLogic]]
subDisjunctions = subformulas (:||:) . disjunctions

subConjunctions :: SLogic -> [[SLogic]]
subConjunctions = subformulas (:&&:) . conjunctions

subformulas :: (a -> a -> a) -> [a] -> [[a]]
subformulas _  []     = []
subformulas _  [x]    = [[x]]
subformulas op (x:xs) = map (x:) yss ++ [ op x y : ys| y:ys <- yss ]
 where
   yss = subformulas op xs