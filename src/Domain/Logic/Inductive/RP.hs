module Domain.Logic.Inductive.RP 
   ( GRelProof, Step, Motivation, showGRelProofWith
   , grelProofDecoder
   , isOpen, isClosed, topExpr, bottomExpr, close, closeEq
   , allRelTypes, allExprs, replaceType
   , eqRelProofBy, proofDecoder, relationToProof
   , updateMiddle, replaceMiddle
   , extendUpper, extendLower, fromDerivation, fromDerivationWith
   , triplesInProof, triplesInProofDirection
   , makeRelProof
   ) where

import Ideas.Common.Derivation
import Control.Applicative
import Data.Maybe
import Ideas.Text.JSON
import Ideas.Utils.Prelude (readM)
import Domain.Logic.Inductive.Relation
import Ideas.Common.Rewriting

gapString, closeString :: String
gapString   = "<GAP>"
closeString = "<CLOSE>" 

type Step = (RelType, Motivation)

type Motivation = String

data GRelProof a
   = Open   (Derivation Step a) RelType (Derivation Step a)
   | Closed (Derivation Step a)
 deriving Eq

instance (Show a, Eq a) => Show (GRelProof a) where
   show = showGRelProofWith show

instance Functor GRelProof where
   fmap f (Open up t lw) = Open (fmap f up) t (fmap f lw)
   fmap f (Closed d)     = Closed (fmap f d)

instance (Eq a, InJSON a) => InJSON (GRelProof a) where
   toJSON = Array . derivationToList forStep toJSON . toDerivation
    where   
      forStep (tp, mot) = 
         Object [("type", String $ show tp), ("motivation", String mot)]

   jsonDecoder = grelProofDecoder True

grelProofDecoder :: (Eq a, InJSON a) => Bool -> DecoderJSON (GRelProof a)
grelProofDecoder autoClose =
   derivationToGRelProof autoClose <$> jArray (derivationDecoder typeAndMotivation jsonDecoder <* jEmpty)

derivationToGRelProof :: Eq a => Bool -> Derivation Step a -> GRelProof a
derivationToGRelProof autoClose d = 
   -- a special string is used for finding the gap in the proof
   case splitStep ((`elem` [gapString, closeString]) . snd) d of
      Just (up, (t, _), lw)
         | autoClose -> closeWhenEq (Open up t lw)
         | otherwise -> Open up t lw
      Nothing -> Closed d

showGRelProofWith :: Eq a => (a -> String) -> GRelProof a -> String
showGRelProofWith f = unlines . derivationToList forStep f . toDerivation
 where
   forStep (tp, mot) = "   " ++ show tp ++ " " ++ mot

toDerivation :: Eq a => GRelProof a -> Derivation Step a
toDerivation (Open up t lw) = 
   case mergeBy True (==) up lw of
      Just _  -> mergeStep up (t, closeString) lw 
      Nothing -> mergeStep up (t, gapString) lw
toDerivation (Closed d) = d

typeAndMotivation :: DecoderJSON (RelType, Motivation)
typeAndMotivation = jObject ((,) <$> getType <*> getMotivation)
 where
   getType = jKey "type" jString >>= maybe (error "getType") return . readM
   getMotivation = jKey "motivation" jString

instance IsTerm a => IsTerm (GRelProof a) where
   toTerm (Open up rt lw) = TCon relProofOpenSymbol
      [ toTerm up
      , toTerm rt
      , toTerm lw
      ]
   toTerm (Closed d) = TCon relProofClosedSymbol [toTerm d] 

   termDecoder 
      =  tCon3 relProofOpenSymbol Open termDecoder termDecoder termDecoder
     <|> tCon1 relProofClosedSymbol Closed termDecoder

relProofOpenSymbol, relProofClosedSymbol :: Symbol
relProofOpenSymbol   = newSymbol "relproof.open"
relProofClosedSymbol = newSymbol "relproof.closed"   

------------------------------------------------------

eqRelProofBy :: (a -> a -> Bool) -> GRelProof a -> GRelProof a -> Bool
eqRelProofBy f (Open up1 rt1 lw1) (Open up2 rt2 lw2) = 
   eqDerivationBy f up1 up2 &&
   rt1 == rt2 &&
   eqDerivationBy f lw1 lw2
eqRelProofBy f (Closed d1) (Closed d2) = 
   eqDerivationBy f d1 d2
eqRelProofBy _ _ _ = False

proofDecoder :: Eq a => DecoderJSON a -> DecoderJSON (GRelProof a)
proofDecoder p = fromDerivation <$> jArray rec
 where
   rec = do
      a <- p 
      curry prepend a <$> jObject stepDecoder <*> rec
         <|> emptyDerivation a <$ jEmpty

   stepDecoder :: DecoderJSON Step
   stepDecoder = (,) <$> relTypeDecoder <*> jKey "motivation" jString

------------------------------------------------------

relationToProof :: Relation RelType a -> GRelProof a
relationToProof rel = 
   Open (emptyDerivation (leftHandSide rel)) (relationType rel) (emptyDerivation (rightHandSide rel))

isOpen :: GRelProof a -> Maybe (a, RelType, a)
isOpen (Open up rt lw) = Just (lastTerm up, rt, firstTerm lw)
isOpen _               = Nothing

isClosed :: GRelProof a -> Maybe (Derivation Step a)
isClosed (Closed d) = Just d
isClosed _          = Nothing

topExpr, bottomExpr :: GRelProof a -> a
topExpr    (Open up _ _) = firstTerm up
topExpr    (Closed d)    = firstTerm d
bottomExpr (Open _ _ lw) = lastTerm lw
bottomExpr (Closed d)    = lastTerm d

close :: Motivation -> GRelProof a -> Maybe (GRelProof a)
close m (Open up t lw) =
   Just $ Closed $ mergeStep up (t, m) lw
close _ _ = Nothing

closeEq :: Bool -> (a -> a -> Bool) -> GRelProof a -> Maybe (GRelProof a)
closeEq keepUpper eq (Open up _ lw) = 
   Closed <$> mergeBy keepUpper eq up lw
closeEq _ _ _ = Nothing

allRelTypes :: GRelProof a -> [RelType]
allRelTypes (Open up rt lw) = 
   map fst (steps up) ++ rt : map fst (steps lw)
allRelTypes (Closed d) = map fst (steps d)

allExprs :: GRelProof a -> [a]
allExprs (Open up _ lw) = terms up ++ terms lw
allExprs (Closed d)     = terms d

replaceType :: RelType -> GRelProof a -> GRelProof a
replaceType tp (Open up _ lw) = Open up tp lw
replaceType _ rp = rp

updateMiddle :: ((a, RelType, a) -> (a, RelType, a)) -> GRelProof a -> Maybe (GRelProof a)
updateMiddle _ (Closed _) = Nothing
updateMiddle f (Open up rt lw) = Just (Open (updateLastTerm (const x) up) t (updateFirstTerm (const y) lw))
 where
   middle = (lastTerm up, rt, firstTerm lw)
   (x, t, y) = f middle

replaceMiddle :: (a, RelType, a) -> GRelProof a -> Maybe (GRelProof a)
replaceMiddle = updateMiddle . const

extendUpper :: Step -> a -> GRelProof a -> Maybe (GRelProof a)
extendUpper step a (Open up rt lw) = Just $ Open (extend up (step, a)) rt lw
extendUpper _ _ _ = Nothing

extendLower :: Step -> a -> GRelProof a -> Maybe (GRelProof a)
extendLower step a (Open up rt lw) = Just $ Open up rt (prepend (a, step) lw)
extendLower _ _ _ = Nothing

-- a special string is used for finding the gap in the proof
fromDerivation :: Eq a => Derivation Step a -> GRelProof a
fromDerivation = fromDerivationWith (`elem` [gapString, closeString])

fromDerivationWith :: Eq a => (Motivation -> Bool) -> Derivation Step a -> GRelProof a
fromDerivationWith isGap d =
   case splitStep (isGap . snd) d of
      Just (up, (t, _), lw) -> closeWhenEq (Open up t lw)
      Nothing -> Closed d

closeWhenEq :: Eq a => GRelProof a -> GRelProof a
closeWhenEq rp = fromMaybe rp (closeEq True (==) rp)

triplesInProof :: GRelProof a -> [(a, Step, a)]
triplesInProof = map snd . triplesInProofDirection

-- direction: true = top-down, false = bottom-up
triplesInProofDirection :: GRelProof a -> [(Bool, (a, Step, a))]
triplesInProofDirection (Open up _ lw) = [ (True, x) | x <- triples up ] ++ [ (False, x) | x <- triples lw ]
triplesInProofDirection (Closed d)     = [ (True, x) | x <- triples d ]

makeRelProof :: RelType -> a -> a -> GRelProof a
makeRelProof tp x y = Open (emptyDerivation x) tp (emptyDerivation y)