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
-- Rewrite rules in the logic domain (including all the rules from the
-- DWA course)
--
-----------------------------------------------------------------------------

module Domain.Logic.Rules
   ( ruleAbsorpAnd, ruleAbsorpOr, ruleDistrAnd, ruleDistrOr
   , ruleComplAnd, ruleComplOr, ruleDeMorganAnd, ruleDeMorganOr
   , ruleDefEquiv, ruleDefImpl
   , ruleFalseAnd, ruleFalseOr, ruleIdempAnd, ruleIdempOr
   , ruleNotFalse, ruleDoubleNeg, ruleNotTrue
   , ruleTrueAnd, ruleTrueOr
   , ruleCommOr, ruleCommAnd, ruleAssocOr, ruleAssocAnd
   ) where

import Domain.Logic.Formula
import Domain.Logic.Generator()
import Domain.Logic.Utils
import Ideas.Common.Library hiding (ruleList)

rule :: RuleBuilder f a => String -> f -> Rule a
rule = rewriteRule . (propositionalId #)

ruleFor :: RuleBuilder f a => Id -> String -> f -> Rule a
ruleFor group s = siblingOf group . rule s

ruleList :: RuleBuilder f a => String -> [f] -> Rule a
ruleList = rewriteRules . (propositionalId #)

ruleListFor :: RuleBuilder f a => Id -> String -> [f] -> Rule a
ruleListFor group s = siblingOf group . ruleList s

-----------------------------------------------------------------------------
-- Commutativity

ruleCommOr :: Rule SLogic
ruleCommOr = ruleFor groupCommutativity "CommOr" $
   \x y -> x :||: y  :~>  y :||: x

ruleCommAnd :: Rule SLogic
ruleCommAnd = ruleFor groupCommutativity "CommAnd" $
   \x y -> x :&&: y  :~>  y :&&: x

-----------------------------------------------------------------------------
-- Associativity (implicit)

ruleAssocOr :: Rule SLogic
ruleAssocOr = minor $ ruleFor groupAssociativity "AssocOr" $
   \x y z -> (x :||: y) :||: z  :~>  x :||: (y :||: z)

ruleAssocAnd :: Rule SLogic
ruleAssocAnd = minor $ ruleFor groupAssociativity "AssocAnd" $
   \x y z -> (x :&&: y) :&&: z  :~>  x :&&: (y :&&: z)

-----------------------------------------------------------------------------
-- Distributivity

ruleDistrAnd :: Rule SLogic
ruleDistrAnd = ruleListFor groupDistribution "AndOverOr"
   [ \x y z -> x :&&: (y :||: z)  :~>  (x :&&: y) :||: (x :&&: z)
   , \x y z -> (x :||: y) :&&: z  :~>  (x :&&: z) :||: (y :&&: z)
   , \x y z -> (x :||: y) :&&: z  :~>  (z :&&: x) :||: (z :&&: y)
   , \x y z -> x :&&: (y :||: z)  :~>  (y :&&: x) :||: (z :&&: x)
   ]

ruleDistrOr :: Rule SLogic
ruleDistrOr = ruleListFor groupDistribution "OrOverAnd"
   [ \x y z -> x :||: (y :&&: z)  :~>  (x :||: y) :&&: (x :||: z)
   , \x y z -> (x :&&: y) :||: z  :~>  (x :||: z) :&&: (y :||: z)
   , \x y z -> x :||: (y :&&: z)  :~>  (y :||: x) :&&: (z :||: x)
   , \x y z -> (x :&&: y) :||: z  :~>  (z :||: x) :&&: (z :||: y)
   ]

-----------------------------------------------------------------------------
-- Idempotency

ruleIdempOr :: Rule SLogic
ruleIdempOr = ruleFor groupIdempotency "IdempOr" $
   \x -> x :||: x  :~>  x

ruleIdempAnd :: Rule SLogic
ruleIdempAnd = ruleFor groupIdempotency "IdempAnd" $
   \x -> x :&&: x  :~>  x

-----------------------------------------------------------------------------
-- Absorption

ruleAbsorpOr :: Rule SLogic
ruleAbsorpOr = ruleListFor groupAbsorption "AbsorpOr"
   [ \x y -> x :||: (x :&&: y)  :~>  x
   , \x y -> x :||: (y :&&: x)  :~>  x
   , \x y -> (x :&&: y) :||: x  :~>  x
   , \x y -> (y :&&: x) :||: x  :~>  x
   ]

ruleAbsorpAnd :: Rule SLogic
ruleAbsorpAnd = ruleListFor groupAbsorption "AbsorpAnd"
   [ \x y -> x :&&: (x :||: y)  :~>  x
   , \x y -> x :&&: (y :||: x)  :~>  x
   , \x y -> (x :||: y) :&&: x  :~>  x
   , \x y -> (y :||: x) :&&: x  :~>  x
   ]

-----------------------------------------------------------------------------
-- True-properties

ruleTrueOr :: Rule SLogic
ruleTrueOr = ruleListFor groupTrueDisjunction "TrueZeroOr"
   [ \x -> T :||: x  :~>  T
   , \x -> x :||: T  :~>  T
   ]

ruleTrueAnd :: Rule SLogic
ruleTrueAnd = ruleListFor groupTrueConjunction "TrueZeroAnd"
   [ \x -> T :&&: x  :~>  x
   , \x -> x :&&: T  :~>  x
   ]

ruleComplOr :: Rule SLogic
ruleComplOr = ruleListFor groupTrueComplement "ComplOr"
   [ \x -> x :||: Not x  :~>  T
   , \x -> Not x :||: x  :~>  T
   ]

ruleNotTrue :: Rule SLogic
ruleNotTrue = ruleFor groupNotTrue "NotTrue" $
   Not T  :~>  F

-----------------------------------------------------------------------------
-- False-properties

ruleFalseOr :: Rule SLogic
ruleFalseOr = ruleListFor groupFalseDisjunction "FalseZeroOr"
   [ \x -> F :||: x  :~>  x
   , \x -> x :||: F  :~>  x
   ]

ruleFalseAnd :: Rule SLogic
ruleFalseAnd = ruleListFor groupFalseConjunction "FalseZeroAnd"
   [ \x -> F :&&: x  :~>  F
   , \x -> x :&&: F  :~>  F
   ]

ruleComplAnd :: Rule SLogic
ruleComplAnd = ruleListFor groupFalseComplement "ComplAnd"
   [ \x -> x :&&: Not x  :~>  F
   , \x -> Not x :&&: x  :~>  F
   ]

ruleNotFalse :: Rule SLogic
ruleNotFalse = ruleFor groupNotFalse "NotFalse" $
   Not F  :~>  T

-----------------------------------------------------------------------------
-- Double negation

ruleDoubleNeg :: Rule SLogic
ruleDoubleNeg = ruleFor groupDoubleNegation "NotNot" $
   \x -> Not (Not x)  :~>  x

-----------------------------------------------------------------------------
-- De Morgan

ruleDeMorganOr :: Rule SLogic
ruleDeMorganOr = ruleFor groupDeMorgan "DeMorganOr" $
   \x y -> Not (x :||: y)  :~>  Not x :&&: Not y

ruleDeMorganAnd :: Rule SLogic
ruleDeMorganAnd = ruleFor groupDeMorgan "DeMorganAnd" $
   \x y -> Not (x :&&: y)  :~>  Not x :||: Not y

-----------------------------------------------------------------------------
-- Implication elimination

ruleDefImpl :: Rule SLogic
ruleDefImpl = ruleFor groupImplication "DefImpl" $
   \x y -> x :->: y  :~>  Not x :||: y

-----------------------------------------------------------------------------
-- Equivalence elimination

ruleDefEquiv :: Rule SLogic
ruleDefEquiv = ruleFor groupEquivalence "DefEquiv" $
   \x y -> x :<->: y  :~>  (x :&&: y) :||: (Not x :&&: Not y)