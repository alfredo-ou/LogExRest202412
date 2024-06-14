{-# LANGUAGE DeriveDataTypeable #-}
module Domain.Logic.Axiomatic.Statement where

import Data.List
import Data.String
import Ideas.Common.Library
import Ideas.Text.JSON
import Ideas.Text.Latex
import Domain.Logic.Formula
import Domain.Logic.Parser
import qualified Data.Set as S
import Data.Typeable

infix 2 :|-, |-
 
data Statement = (:|-) { assumptions :: S.Set SLogic, consequent :: SLogic }
   deriving (Eq, Ord, Typeable)

(|-) :: [SLogic] -> SLogic -> Statement
xs |- p = S.fromList xs :|- p

addAssumption :: SLogic -> Statement -> Statement
addAssumption p (ps :|- q) = S.insert p ps :|- q

instance Show Statement where
   show (ps :|- q) = intercalate ", " (map show (S.toList ps)) ++ 
                     " |- " ++ show q

instance Read Statement where
   readsPrec _ s =
      case parseStatement False s of
         Left _ -> []
         Right (ps, q) -> [(ps |- q, "")]

instance Reference Statement

instance IsTerm Statement where
   toTerm st = binary statementSymbol (toTerm (S.toList (assumptions st))) (toTerm (consequent st))
   termDecoder = tCon2 statementSymbol (|-) termDecoder termDecoder
   
instance InJSON Statement where
   toJSON = toJSON . show
   jsonDecoder = jString >>= \s -> 
      case readM s of
         Just a  -> return a
         Nothing -> errorStr "invalid statement"

instance ToLatex Statement where
   toLatex st = commas (map slogicToLatex (S.toList (assumptions st)))
                   <> command "vdash" <> slogicToLatex (consequent st)

slogicToLatex :: SLogic -> Latex
slogicToLatex = fromString . show

statementSymbol :: Symbol
statementSymbol = newSymbol "logic.propositional.axiomatic.statement"

subStatement :: Statement -> Statement -> Bool
subStatement (ps :|- p) (qs :|- q) = ps `S.isSubsetOf` qs && p == q

validStatement :: Statement -> Bool
validStatement st =
   tautology (ands (S.toList (assumptions st)) :->: consequent st)
         