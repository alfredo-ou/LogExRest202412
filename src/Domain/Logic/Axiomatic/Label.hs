module Domain.Logic.Axiomatic.Label 
   ( AxiomaticLabel(..)
   , logax, assumpId, lemmaId, axiomAId, axiomBId, axiomCId, mpId, dedId
   ) where

import Ideas.Common.Id
import Ideas.Common.Rewriting
import Ideas.Text.JSON
import Ideas.Text.Latex
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Domain.Logic.Axiomatic.Motivation

data AxiomaticLabel a = Assumption | Lemma | AxiomA | AxiomB | AxiomC | ModusPonens a a | Deduction a
   deriving (Eq, Ord)

instance Show a => Show (AxiomaticLabel a) where
   show = show . toMotivation

instance Read a => Read (AxiomaticLabel a) where
   readsPrec i s = 
      [ (l, rest)
      | (m, rest) <- readsPrec i s
      , l <- maybeToList (fromMotivation m)
      ]

instance Functor AxiomaticLabel where
   fmap = fmapDefault

instance Foldable AxiomaticLabel where
   foldMap f l =
      case l of
         ModusPonens x y -> f x <> f y
         Deduction x     -> f x
         _               -> mempty

instance Traversable AxiomaticLabel where
   traverse f l =
      case l of
         Assumption      -> pure Assumption
         Lemma           -> pure Lemma
         AxiomA          -> pure AxiomA
         AxiomB          -> pure AxiomB
         AxiomC          -> pure AxiomC
         ModusPonens x y -> ModusPonens <$> f x <*> f y
         Deduction x     -> Deduction   <$> f x

instance IsId (AxiomaticLabel a) where
   newId = newId . toMotivation

instance IsTerm a => IsTerm (AxiomaticLabel a) where
   toTerm = toTerm . toMotivation
   termDecoder = do
      m <- termDecoder
      case fromMotivation m of
         Just a -> return a
         Nothing -> errorStr "invalid axiomatic label"

instance InJSON a => InJSON (AxiomaticLabel a) where
   toJSON = toJSON . toMotivation
   jsonDecoder = jsonDecoder >>= \m ->
      case fromMotivation m of
         Just a  -> return a
         Nothing -> errorStr "invalid axiomatic label"

instance ToLatex a => ToLatex (AxiomaticLabel a) where
   toLatex = toLatex . toMotivation

-----------------------------------------------------------------------
-- Conversion to/from Motivation

toMotivation :: AxiomaticLabel a -> Motivation a
toMotivation l =
   case l of
      Assumption      -> f assumpId []
      Lemma           -> f lemmaId []
      AxiomA          -> f axiomAId []
      AxiomB          -> f axiomBId []
      AxiomC          -> f axiomCId []
      ModusPonens x y -> f mpId [x, y]
      Deduction x     -> f dedId [x]
 where
   f = motivation . unqualified

fromMotivation :: Motivation a -> Maybe (AxiomaticLabel a)
fromMotivation m = 
   case toList m of
      []     | f assumpId -> Just Assumption
             | f lemmaId  -> Just Lemma
             | f axiomAId -> Just AxiomA
             | f axiomBId -> Just AxiomB
             | f axiomCId -> Just AxiomC
      [x]    | f dedId    -> Just (Deduction x)
      [x, y] | f mpId     -> Just (ModusPonens x y)
      _ -> Nothing
 where
   f n = unqualified n == unqualified (motivationId m)

-----------------------------------------------------------------------
-- Symbols

logax :: Id
logax = newId "logic.propositional.axiomatic"

assumpId, lemmaId, axiomAId, axiomBId, axiomCId, mpId, dedId :: Id
assumpId = logax # "assumption"
lemmaId  = logax # "lemma"
axiomAId = logax # "axiom-a"
axiomBId = logax # "axiom-b"
axiomCId = logax # "axiom-c"
mpId     = logax # "modusponens"
dedId    = logax # "deduction"