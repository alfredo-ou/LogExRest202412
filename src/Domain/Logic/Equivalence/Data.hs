{-# LANGUAGE FlexibleInstances #-}
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

module Domain.Logic.Equivalence.Data 
   ( Proof, makeProof, showProof, proofIsReady
   , equivalentProofs, similarProofs, checkEqForStepsInProof
     -- direction
   , Direction(..), directionRef
   , liftPair'
     -- unicode support
   , showProofUnicode, jsonUnicodeEncodingProof, jsonEncodingProof
   ) where

import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.Relation
import Domain.Logic.Generator (equalLogicA)
import Ideas.Encoding.Encoder
import Ideas.Common.Library
import Ideas.Text.JSON
import Data.Maybe

type Proof = GRelProof SLogic

makeProof :: (SLogic, SLogic) -> Proof
makeProof (p, q) = makeRelProof Equal p q

showProof :: Proof -> String
showProof = showGRelProofWith ppLogic

proofIsReady :: Proof -> Bool
proofIsReady = maybe True f . isOpen
 where
   f (p, _, q) = equalLogicA p q

-- moeten alle stappen altijd gecontroleerd worden?
equivalentProofs :: Proof -> Proof -> Bool
equivalentProofs proof1 proof2 =
   eqLogic (topExpr proof1) (topExpr proof2) &&
   eqLogic (bottomExpr proof1) (bottomExpr proof2) &&
   checkEqForStepsInProof proof1 && checkEqForStepsInProof proof2

checkEqForStepsInProof :: Proof -> Bool
checkEqForStepsInProof proof = pairWiseEq (allExprs proof)
 where
   pairWiseEq xs = and $ zipWith eqLogic xs (drop 1 xs)

similarProofs :: Proof -> Proof -> Bool
similarProofs proof1 proof2 =
   length xs == length ys && myClosed proof1 == myClosed proof2 && and (zipWith equalLogicA xs ys)
 where
   myClosed = maybe True (\(up, _, lw) -> up == lw) . isOpen

   xs = allExprs proof1
   ys = allExprs proof2

-- orphan instance
instance InJSON SLogic where
   toJSON = toJSON . ppLogic
   jsonDecoder = jString >>= either error return . parseLogicPars

-----------------------------------------------------------------------

data Direction = TopDown | BottomUp
   deriving (Eq, Ord, Enum) -- 0=top-down, 1=bottom-up

instance Show Direction where
   show = show . fromEnum

instance Read Direction where
   readsPrec i s = [ (toEnum n, rest) | (n, rest) <- readsPrec i s ]

instance IsTerm Direction where
   toTerm = toTerm . fromEnum
   termDecoder = toEnum <$> termDecoder

instance Reference Direction

directionRef :: Ref Direction
directionRef = makeRef "direction"

-----------------------------------------------------------------------
-- Lifting of rules

liftPair' :: Rule (SLogic, SLogic) -> Rule (Context Proof)
liftPair' r = liftWithM f r
 where
   f ctx = do
      prf <- fromContext ctx
      (p, _, q) <- isOpen prf
      let make (p', q')
             | p /= p'   = extendProof TopDown p'
             | q /= q'   = extendProof BottomUp q'
             | otherwise = error "liftPair: no changes"
      return ((p, q), \new -> make new (showId r) ctx)

liftDirection :: Direction -> Rule SLogic -> Rule (Context Proof)
liftDirection TopDown  = liftTopDown
liftDirection BottomUp = liftBottomUp

liftTopDown :: Rule SLogic -> Rule (Context Proof)
liftTopDown r = liftWithM f r
 where
   f ctx = do 
      prf <- fromContext ctx
      (p, _, _) <- isOpen prf
      return (p, \q -> extendProof TopDown q (showId r) ctx)

liftBottomUp :: Rule SLogic -> Rule (Context Proof)
liftBottomUp r = liftWithM f r
 where
   f ctx = do 
      prf <- fromContext ctx
      (_, _, p) <- isOpen prf
      return (p, \q -> extendProof BottomUp q (showId r) ctx)

extendProof :: Direction -> SLogic -> Motivation -> Context Proof -> Context Proof
extendProof dir p m ctx = 
   replaceInContext (fromJust $ f dir (Equal, m) p $ fromJust $ fromContext ctx) (insertRef directionRef dir ctx)
 where
   f TopDown  = extendUpper
   f BottomUp = extendLower

-----------------------------------------------------------------------
-- Unicode support

newtype Unicode a = Unicode { fromUnicode :: a }
 deriving Eq

instance InJSON (Unicode SLogic) where
   toJSON = toJSON . ppLogicUnicode . fromUnicode
   jsonDecoder = jString >>= either error (return . Unicode) . parseLogicUnicodePars

jsonEncodingProof :: Exercise Proof -> Exercise Proof
jsonEncodingProof = addJSONView (makeView fromJSONProof toJSON)

jsonUnicodeEncodingProof :: Exercise Proof -> Exercise Proof
jsonUnicodeEncodingProof = addJSONView (makeView fromJSONUnicode toJSONUnicode)

toJSONUnicode :: Proof -> JSON
toJSONUnicode = toJSON . fmap Unicode

fromJSONUnicode :: JSON -> Maybe Proof
fromJSONUnicode = fmap (fmap fromUnicode) . either (fail . show) return . evalDecoderJSON (grelProofDecoder False)

fromJSONProof:: JSON -> Maybe Proof
fromJSONProof = either (fail . show) return . evalDecoderJSON (grelProofDecoder False)

showProofUnicode :: Proof -> String
showProofUnicode = showGRelProofWith ppLogicUnicode