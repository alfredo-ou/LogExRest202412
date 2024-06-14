module Domain.Logic.Inductive.Theorem 
   ( Theorem, makeTheorem
   , theoremToJSON, theoremDecoder
   , (.==.), (.<=.), (.<.), (.<==>.), (.>.)
   , relationTypeForTheorem, instantiate, keepsMetaVars
   , Substitution
   , matchTheorem, matchLhs, matchRhs
   ) where

import Data.Maybe
import Ideas.Utils.Uniplate
import Ideas.Text.JSON
import Ideas.Common.Rewriting
import Domain.Logic.Inductive.Parser
import Domain.Math.Expr
import Domain.Logic.Inductive.Relation

newtype Theorem = T (Relation RelType Term)
 deriving (Show, Eq)

instance IsTerm Theorem where 
   toTerm (T r) = toTerm r
   termDecoder = T <$> termDecoder

theoremToJSON :: Theorem -> JSON
theoremToJSON th = Array
   [ String $ show (leftHandSide rel)
   , Object [("type", String $ show $ relationType rel)]
   , String $ show (rightHandSide rel)
   ]
 where
   rel = instantiate (Var "phi") th

theoremDecoder :: DecoderJSON Theorem
theoremDecoder = jArray (flip makeTheorem <$> exprDecoder <*> jObject relTypeDecoder <*> exprDecoder <* jEmpty)

-- assume quantification over 'phi'
makeTheorem :: RelType -> Expr -> Expr -> Theorem
makeTheorem tp x y = T (makeRelation tp (f (toTerm x)) (f (toTerm y)))
 where
   f (TVar "phi") = TMeta 0
   f t = descend f t

infix 1 .==., .<=., .<., .<==>., .>.
 
(.==.), (.<=.), (.<.), (.<==>.) :: Expr -> Expr -> Theorem
(.==.)   = makeTheorem Equal
(.<=.)   = makeTheorem LessThanOrEqual
(.<.)    = makeTheorem LessThan
(.>.)    = makeTheorem GreaterThan
(.<==>.) = makeTheorem Equivalence

relationTypeForTheorem :: Theorem -> RelType
relationTypeForTheorem (T r) = relationType r

instantiate :: Expr -> Theorem -> Relation RelType Expr
instantiate e (T r) = fmap (fromJust . fromTerm . f) r
 where
    f (TMeta 0) = toTerm e
    f t = descend f t

-- left-hand side and right-hand side of theorem have the same metavars
keepsMetaVars :: Theorem -> Bool
keepsMetaVars (T r) = metaVarSet (leftHandSide r) == metaVarSet (rightHandSide r)

type Substitution = [(Int, Term)]

matchTheorem :: Theorem -> Expr -> Expr -> Maybe Substitution
matchTheorem (T r) x y = 
   matchTerms [leftHandSide r, rightHandSide r] [toTerm x, toTerm y]

matchLhs :: Theorem -> Expr -> Maybe (Substitution, Expr)
matchLhs (T r) x = do
   sub <- matchTerm (leftHandSide r) (toTerm x)
   -- the substitution should replace ALL meta variables, otherwise fromTerm will fail!
   rhs <- fromTerm (sub |-> rightHandSide r)
   return (sub, rhs)

matchRhs :: Theorem -> Expr -> Maybe Substitution
matchRhs (T r) x =
   matchTerm (rightHandSide r) (toTerm x)

-- to do: respect associativity and commutativity when matching
matchTerm :: Term -> Term -> Maybe Substitution
matchTerm (TCon s1 xs) (TCon s2 ys) 
   | s1 == s2 = matchTerms xs ys
matchTerm (TList xs) (TList ys) = matchTerms xs ys
matchTerm (TMeta n) t = Just [(n, t)]
matchTerm t1 t2 = if t1 == t2 then return [] else Nothing

matchTerms :: [Term] -> [Term] -> Maybe Substitution
matchTerms [] [] = Just []
matchTerms (x:xs) (y:ys) = do
   s1 <- matchTerm x y
   s2 <- matchTerms (map (s1 |->) xs) (map (s1 |->) ys)
   return (s1 ++ s2)
matchTerms _ _ = Nothing

(|->) :: Substitution -> Term -> Term
sub |-> TMeta n = fromMaybe (TMeta n) (lookup n sub)
sub |-> t       = descend (sub |->) t