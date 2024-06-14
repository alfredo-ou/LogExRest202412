module Domain.Logic.Axiomatic.ProofDAG 
   ( ProofDag, proofDagToList, (==>), proofterms
   , trimProofDag, trimMotivations
   , depends, findMotivation, filterNode
   ) where

import Data.Foldable
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

infix 1 ==>

newtype ProofDag l a = PD (M.Map a (S.Set (l a)))
 deriving Eq
   
proofDagToList :: ProofDag l a -> [(a, l a)]
proofDagToList (PD m) = 
   [ (a, mot)
   | (a, ms) <- M.toList m
   , mot <- S.toList ms
   ]

instance (Show (l a), Ord a, Show a) => Show (ProofDag l a) where
   show (PD m) = unlines $ 
      [ show a ++ "   " ++ show mot
      | (a, ms) <- M.toList m, mot <- S.toList ms 
      ]

instance (Ord (l a), Ord a) => Semigroup (ProofDag l a) where
   PD m1 <> PD m2 = PD (M.unionWith (<>) m1 m2)
 
instance (Ord (l a), Ord a) => Monoid (ProofDag l a) where
   mempty = PD mempty
   mappend = (<>)

(==>) :: Ord a => a -> l a -> ProofDag l a
a ==> mot = PD (M.singleton a (S.singleton mot))

proofterms :: Ord a => ProofDag l a -> [a]
proofterms = S.toList . prooftermSet

prooftermSet :: Ord a => ProofDag l a -> S.Set a
prooftermSet (PD m) = M.keysSet m
                   
findMotivation :: Ord a => a -> ProofDag l a -> l a
findMotivation a (PD m) = head $ S.toList $ fromJust $ M.lookup a m

trimMotivations :: Foldable l => ProofDag l a -> ProofDag l a
trimMotivations (PD m) = PD $ M.map f m
 where
   f s = if S.null s1 then s2 else s1
    where 
      (s1, s2) = S.partition (null . toList) s

trimProofDag :: (Foldable l, Ord a) => [a] -> ProofDag l a -> ProofDag l a
trimProofDag goals dag@(PD m)
   | S.null removals = dag
   | otherwise       = trimProofDag goals trimmed
  where 
    used = S.fromList (concatMap f (M.elems m))
    f ms = concatMap toList (S.toList ms)
    removals  = S.filter notUsed (M.keysSet m)
    notUsed a = not (a `S.member` used) && a `notElem` goals
    trimmed   = PD $ M.filterWithKey (\k _ -> not (k `S.member` removals)) m

filterNode :: (a -> Bool) -> ProofDag l a -> ProofDag l a
filterNode p (PD m) = PD $ M.filterWithKey (\a _ -> p a) m

-------------------------------------------------------------------------------------------   

depends :: (Foldable l, Ord a) => ProofDag l a -> a -> S.Set a
depends (PD m) = S.fromList . rec
 where
   rec a = a : 
      [ c
      | b <- maybe [] (concatMap toList . S.toList) (M.lookup a m)
      , c <- rec b
      ]

{- analyse dependencies (and approximate minimal length)

analyse :: (Foldable l, Show a, Eq a) => ProofDag l a -> [(a, Int)]
analyse (PD m) = error $ show $ rec [] (M.toList m)
 where
   rec acc xs
      | null new  = acc
      | otherwise = rec (acc ++ new) ys
    where
      (new, ys) = partitionEithers (map f xs)
      
      f (a, ms) = 
         case mapMaybe g (S.toList ms) of
            [] -> Right (a, ms)
            is -> Left (a, minimum is)

      g m = do
         is <- mapM (`lookup` acc) (toList m)
         Just (sum is + 1)
-}