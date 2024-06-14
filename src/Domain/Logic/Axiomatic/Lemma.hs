module Domain.Logic.Axiomatic.Lemma 
   ( Lemmas, Lemma, lemma, instantiate
   ) where

import Domain.Logic.Axiomatic.Statement
import Ideas.Common.Rewriting
import Ideas.Text.JSON

type Lemmas = [Lemma]

newtype Lemma = Lemma Statement

instance Show Lemma where
   show (Lemma st) = "Lemma: " ++ show st

instance IsTerm Lemma where
   toTerm (Lemma st) = toTerm st
   termDecoder = Lemma <$> termDecoder

instance InJSON Lemma where
   toJSON (Lemma st) = toJSON st
   jsonDecoder =Lemma <$> jsonDecoder

lemma :: Statement -> Lemma
lemma st 
   | validStatement st = Lemma st
   | otherwise = error $ "Invalid lemma: " ++ show st

instantiate :: Lemma -> Statement
instantiate (Lemma st) = st