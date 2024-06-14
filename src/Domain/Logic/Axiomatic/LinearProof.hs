{-# LANGUAGE GADTs #-}
module Domain.Logic.Axiomatic.LinearProof 
   ( -- Types
     Proof
     -- Getters
   , getTerm, getMotivation, getProofline, findInProof, findAllInProof
   , fullyMotivated, isMotivated, isNotMotivated, termsInProof, motivations, isInProof, lastTerm, prooflines
   , keepGrounded, size, numbers, isGrounded
     -- Constructors
   , proofline, addProofline, proofgoal
   , addMotivation
     -- Numbering
   , usedNumbers, nextNumber, nextNumberAfter, prevNumber, prevNumberBefore
     -- Transformations
   , renumber, renumberFrom, removeLine
   ) where

import Control.Applicative
import Data.Bifunctor
import Data.Foldable
import Data.List
import Data.Maybe
import Ideas.Common.Rewriting.Term
import Ideas.Text.JSON
import Ideas.Text.Latex
import qualified Data.Semigroup as SG
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

data Proof l a where
   P :: (Functor l, Foldable l) => IM.IntMap (a, Maybe (l Int)) -> Proof l a

instance (Eq (l Int), Eq a) => Eq (Proof l a) where
      P x == P y = x == y

proofline :: (Foldable l, Functor l) => Int -> a -> l Int -> Proof l a
proofline n a mot = add n a (Just mot) mempty

addProofline :: Int -> a -> l Int -> Proof l a -> Proof l a
addProofline n a = add n a . Just

proofgoal :: (Foldable l, Functor l) => Int -> a -> Proof l a
proofgoal n a = add n a Nothing mempty

-- general (local) constructor
add :: Int -> a -> Maybe (l Int) -> Proof l a -> Proof l a
add n a mot (P m) = P $ IM.insert n (a, mot) m

addMotivation :: Int -> l Int -> Proof l a -> Proof l a
addMotivation n mot (P m) = P $ IM.adjust f n m 
 where
    f (a, _) = (a, Just mot)

instance Functor (Proof l) where
   fmap f (P xs) = P (IM.map (first f) xs)

instance SG.Semigroup (Proof l a) where
   (<>) = merge

instance (Functor l, Foldable l) => Monoid (Proof l a) where
   mempty  = P IM.empty
   mappend = merge

instance (Show (l Int), Show a) => Show (Proof l a) where
   show = unlines . map f . prooflines
    where 
      f (n, (a, maybeMot)) = s2 ++ s4
       where
         s2 = alignr 5 (show n ++ ".") ++ "  " ++ show a
         s3 = maybe "" show maybeMot
         s4 = if null s3 then "" else "  " ++ alignr (70 - length s2) s3
      
      alignr n x = replicate (n - length x) ' ' ++ x

instance (Functor l, Foldable l, InJSON (l Int), InJSON a) => InJSON (Proof l a) where
   toJSON = Array . map f . prooflines
    where
      f (n, (a, maybeMot)) = Object $
         [ ("number", toJSON n)
         , ("term", toJSON a)
         ] ++
         case maybe Null toJSON maybeMot of
            Object xs -> xs
            _ -> []
   
   jsonDecoder = P . IM.fromList <$> jArrayOf decodeLine 
    where
      decodeLine = jObject $ do
         n   <- jKey "number" jInt
         a   <- jKey "term"   jsonDecoder
         mot <- optional jsonDecoder
         return (n, (a, mot))
   
proofSymbol, prooflineSymbol :: Symbol
proofSymbol     = newSymbol "proof"
prooflineSymbol = newSymbol "proofline"

instance (Functor l, Foldable l, IsTerm (l Int), IsTerm a) => IsTerm (Proof l a) where
   toTerm = function proofSymbol . map f . prooflines
    where
      f (n, (a, mot)) = 
         function prooflineSymbol [toTerm n, toTerm a, toTerm mot]
   termDecoder =
      let f n a mot  = (n, (a, mot))
          decodeLine = tCon3 prooflineSymbol f termDecoder termDecoder termDecoder
      in P . IM.fromList <$> tConOf proofSymbol decodeLine

instance (ToLatex (l Int), ToLatex a) => ToLatex (Proof l a) where
   toLatex = array "rll" . map f . prooflines
    where
      f (n, (a, maybeMot)) = [numberTex n, toLatex a, toLatex maybeMot]

      numberTex = toLatex . ((++ ".") . show)

usedNumbers :: Proof l a -> [Int]
usedNumbers (P m) = nub $ concatMap f (IM.toList m)
 where
   f (n, (_, mot)) = n : references mot

nextNumber :: Proof l a -> Int
nextNumber = nextNumberAfter 0

nextNumberAfter :: Int -> Proof l a -> Int
nextNumberAfter n p = head (filter (`notElem` usedNumbers p) [n+1 ..])

prevNumber :: Proof l a -> Int
prevNumber = prevNumberBefore 1001

prevNumberBefore :: Int -> Proof l a -> Int
prevNumberBefore n p = head (filter (`notElem` usedNumbers p) [n-1, n-2 ..])

renumber :: Proof l a -> Proof l a
renumber = renumberFrom 1

renumberFrom :: Int -> Proof l a -> Proof l a
renumberFrom i proof@(P _) = renumberWith f proof
 where
   used = usedNumbers proof
   f    = fromMaybe 0 . (`lookup` zip used [i..])

renumberWith :: (Int -> Int) -> Proof l a -> Proof l a
renumberWith f (P m) = P (IM.map g (IM.mapKeys f m))
 where
   g (a, maybeMot) = (a, fmap (fmap f) maybeMot)

{-
removeLine :: Int -> Proof l a -> Proof l a
removeLine n (P m) = P $ IM.map f $ IM.delete n m
 where
   f (a, maybeMot) = (a, g maybeMot) 
   
   g (Just mot) | n `elem` toList mot = Nothing
   g maybeMot = maybeMot
-}

removeLines :: [Int] -> Proof l a -> Proof l a
removeLines = flip (foldr removeLine)

-- removes one line from the proof
-- for a grounded line: remove that line and lines/motivations that depend on this line (use one forward sweep).
-- for an ungrounded line: determine from its motivation which other lines should be removed (but only in ungrounded part)
-- always keep the goal
removeLine :: Int -> Proof l a -> Proof l a
removeLine n p@(P m) 
    | n `isGoal` p     = p
    | n `isGrounded` p = P $ IM.fromList $ rec [n] $ IM.toList m
    | otherwise = 
         case break ((== n) . fst) (IM.toList m) of
            (_, []) -> p
            (before, (_, (_, mot)):after) -> 
               let is = filter (not . (`isGrounded` p)) (references mot)
               in removeLines is $ P $ IM.fromList $ before ++ map (second (second f)) after
 where
   rec _ [] = []
   rec ns (hd@(i, (a, mot)):rest)
      | any (`elem` ns) (i:mis) = 
           if isGoal i p 
           then (i, (a, Nothing)) : rec ns rest
           else rec (i:ns) rest
      | otherwise  = hd : rec ns rest
    where
      mis = references mot

   f mot = if n `elem` references mot then Nothing else mot

merge :: Proof l a -> Proof l a -> Proof l a
merge (P m1) p2@(P m2)
   | IS.disjoint ns1 ns2 = make p2
   | otherwise = make (renumberFrom (IS.findMax ns1 + 1) p2)
 where
   ns1 = IM.keysSet m1
   ns2 = IM.keysSet m2

   make (P m3) = P (IM.union m1 m3)

findInProof :: Eq a => a -> Proof l a -> Maybe Int
findInProof a = listToMaybe . findAllInProof a

findAllInProof :: Eq a => a -> Proof l a -> [Int]
findAllInProof a = findInProofBy (== a)

findInProofBy :: (a -> Bool) -> Proof l a -> [Int]
findInProofBy cond (P m) = IM.keys (IM.filter (cond . fst) m)

getProofline :: Int -> Proof l a -> Maybe (a, Maybe (l Int))
getProofline n (P m) = IM.lookup n m

getTerm :: Int -> Proof l a -> Maybe a
getTerm n p = fst <$> getProofline n p

getMotivation :: Int -> Proof l a -> Maybe (l Int)
getMotivation n p = getProofline n p >>= snd

-- all proof lines have a motivation
fullyMotivated :: Proof l a -> Bool
fullyMotivated = all (isJust . snd . snd) . prooflines

isMotivated :: Int -> Proof l a -> Bool
isMotivated n = maybe False (isJust . snd) . getProofline n

isNotMotivated :: Int -> Proof l a -> Bool
isNotMotivated n = maybe False (isNothing . snd) . getProofline n

termsInProof :: Proof l a -> [a]
termsInProof = map (fst . snd) . prooflines

motivations :: Proof l a -> [l Int]
motivations = mapMaybe (snd . snd) . prooflines

isInProof :: Eq a => a -> Proof l a -> Bool
isInProof a = isJust . findInProof a

lastTerm :: Proof l a -> Maybe a
lastTerm = listToMaybe . reverse . termsInProof

prooflines :: Proof l a -> [(Int, (a, Maybe (l Int)))]
prooflines (P m) = IM.toList m

-- only keep proof lines that are grounded
keepGrounded :: Proof l a -> Proof l a
keepGrounded (P m) = P $ IM.fromList $ rec [] $ IM.toList m
 where
   rec _ [] = []
   rec is (pl@(n, (_, maybeMot)):rest) = 
      case maybeMot of
         Just mot | all (`elem` is) (toList mot) ->
            pl : rec (n:is) rest
         _ -> rec is rest

size :: Proof l a -> Int
size (P m) = IM.size m

numbers :: Proof l a -> [Int]
numbers (P m) = IM.keys m

isGoal :: Int -> Proof l a -> Bool
isGoal n p = 
   case numbers p of
      [] -> False
      is -> n == maximum is

isGrounded :: Int -> Proof l a -> Bool
isGrounded n = elem n . numbers . keepGrounded

-- local helper
references :: Foldable l => Maybe (l Int) -> [Int]
references = maybe [] toList