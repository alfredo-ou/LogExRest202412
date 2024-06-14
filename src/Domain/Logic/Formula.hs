{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- Copyright 2019, Ideas project team. This file is distributed under the
-- terms of the Apache License 2.0. For more information, see the files
-- "LICENSE.txt" and "NOTICE.txt", which are included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-----------------------------------------------------------------------------

module Domain.Logic.Formula
   ( module Domain.Logic.Formula, module Domain.Algebra.Boolean
   ) where

import Control.Applicative
import Data.Foldable (toList)
import Data.List
import Data.Monoid
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Typeable
import Domain.Algebra.Boolean
import Ideas.Common.Classes
import Ideas.Common.Rewriting hiding (trueSymbol, falseSymbol)
import Ideas.Text.Latex
import Ideas.Utils.Prelude (ShowString, subsets)
import Ideas.Utils.Uniplate
import qualified Ideas.Text.OpenMath.Dictionary.Logic1 as OM

infixr 2 :<->:
infixr 3 :->:
infixr 4 :||:
infixr 5 :&&:

-- | The data type Logic is the abstract syntax for the domain
-- | of logic expressions.
data Logic a = Var a
             | Logic a :->:  Logic a            -- implication
             | Logic a :<->: Logic a            -- equivalence
             | Logic a :&&:  Logic a            -- and (conjunction)
             | Logic a :||:  Logic a            -- or (disjunction)
             | Not (Logic a)                    -- not
             | T                                -- true
             | F                                -- false
 deriving (Eq, Ord, Typeable)

-- | For simple use, we assume the variables to be strings
type SLogic = Logic ShowString

instance Show a => Show (Logic a) where
   show     = ppLogic
   showList = (++) . intercalate ", " . map show

instance Functor Logic where
   fmap = fmapDefault

instance Foldable Logic where
   foldMap = foldMapDefault

instance Traversable Logic where
   traverse f = foldLogic
      ( fmap Var . f, liftA2 (:->:), liftA2 (:<->:), liftA2 (:&&:)
      , liftA2 (:||:), liftA Not, pure T, pure F
      )

instance BoolValue (Logic a) where
   fromBool b = if b then T else F
   isTrue T  = True
   isTrue _  = False
   isFalse F = True
   isFalse _ = False

instance Boolean (Logic a) where
   (<&&>)     = (:&&:)
   (<||>)     = (:||:)
   complement = Not

instance CoBoolean (Logic a) where
   isAnd (p :&&: q)     = Just (p, q)
   isAnd _              = Nothing
   isOr  (p :||: q)     = Just (p, q)
   isOr  _              = Nothing
   isComplement (Not p) = Just p
   isComplement _       = Nothing

instance Container Logic where
   singleton            = Var
   getSingleton (Var a) = Just a
   getSingleton _       = Nothing

instance ToLatex a => ToLatex (Logic a) where
   toLatexPrec = flip (foldLogic alg)
    where
      alg = ( pp, binopN 3 "rightarrow", binopN 0 "leftrightarrow", binopA 2 "wedge"
            , binopA 1 "vee", nott, pp "T", pp "F")
      binopA prio op p q n = parIf (n > prio) (p prio <> command op <> q prio)
      binopN prio op p q n = parIf (n > prio) (p (prio+1) <> command op <> q (prio + 1))
      pp s      = const (toLatex s)
      nott p _  = command "neg" <> p 4
      parIf b   = if b then parens else id

-- | The type LogicAlg is the algebra for the data type Logic
-- | Used in the fold for Logic.
type LogicAlg b a = (b -> a, a -> a -> a, a -> a -> a, a -> a -> a, a -> a -> a, a -> a, a, a)

-- | foldLogic is the standard fold for Logic.
foldLogic :: LogicAlg b a -> Logic b -> a
foldLogic (var, impl, equiv, conj, disj, neg, tr, fl) = rec
 where
   rec logic =
      case logic of
         Var x     -> var x
         p :->: q  -> rec p `impl`  rec q
         p :<->: q -> rec p `equiv` rec q
         p :&&: q  -> rec p `conj`  rec q
         p :||: q  -> rec p `disj`  rec q
         Not p     -> neg (rec p)
         T         -> tr
         F         -> fl

-- | The monadic join for logic
catLogic :: Logic (Logic a) -> Logic a
catLogic = foldLogic (id, (:->:), (:<->:), (:&&:), (:||:), Not, T, F)

-- | evalLogic takes a function that gives a logic value to a variable,
-- | and a Logic expression, and evaluates the boolean expression.
evalLogic :: (a -> Bool) -> Logic a -> Bool
evalLogic env = foldLogic (env, impl, (==), (&&), (||), not, True, False)
 where
   impl p q = not p || q

-- | eqLogic determines whether or not two Logic expression are logically
-- | equal, by evaluating the logic expressions on all valuations.
eqLogic :: Eq a => Logic a -> Logic a -> Bool
eqLogic p q = all (\f -> evalLogic f p == evalLogic f q) fs
 where
   xs = varsLogic p `union` varsLogic q
   fs = map (flip elem) (subsets xs)

tautology :: Eq a => Logic a -> Bool
tautology = eqLogic T

isNot :: Logic a -> Bool
isNot (Not _) = True
isNot _       = False

-- | A Logic expression is atomic if it is a variable or a constant True or False.
isAtomic :: Logic a -> Bool
isAtomic logic =
   case logic of
      Not (Var _) -> True
      _           -> null (children logic)

-- | Functions isDNF, and isCNF determine whether or not a Logix expression
-- | is in disjunctive normal form, or conjunctive normal form, respectively.
isDNF, isCNF :: Logic a -> Bool
isDNF = all isAtomic . concatMap conjunctions . disjunctions
isCNF = all isAtomic . concatMap disjunctions . conjunctions

-- | Count the number of equivalences
countEquivalences :: Logic a -> Int
countEquivalences p = length [ () | _ :<->: _ <- universe p ]

-- | Function varsLogic returns the variables that appear in a Logic expression.
varsLogic :: Eq a => Logic a -> [a]
varsLogic = nub . toList

instance Uniplate (Logic a) where
   uniplate this =
      case this of
         p :->: q  -> plate (:->:)  |* p |* q
         p :<->: q -> plate (:<->:) |* p |* q
         p :&&: q  -> plate (:&&:)  |* p |* q
         p :||: q  -> plate (:||:)  |* p |* q
         Not p     -> plate Not     |* p
         _         -> plate this

instance Different (Logic a) where
   different = (T, F)

instance IsTerm a => IsTerm (Logic a) where
   toTerm = foldLogic
      ( toTerm, binary impliesSymbol, binary equivalentSymbol
      , binary andSymbol, binary orSymbol, unary notSymbol
      , symbol trueSymbol, symbol falseSymbol
      )

   termDecoder
       =  T <$ tCon0 trueSymbol
      <|> F <$ tCon0 falseSymbol
      <|> tCon1 notSymbol Not termDecoder
      <|> tCon2 impliesSymbol (:->:) termDecoder termDecoder
      <|> tCon2 equivalentSymbol (:<->:) termDecoder termDecoder
      <|> ands <$> tConOf andSymbol termDecoder
      <|> ors <$> tConOf orSymbol termDecoder
      <|> Var <$> termDecoder

trueSymbol, falseSymbol, notSymbol, impliesSymbol, equivalentSymbol,
   andSymbol, orSymbol :: Symbol

trueSymbol       = newSymbol OM.trueSymbol
falseSymbol      = newSymbol OM.falseSymbol
notSymbol        = newSymbol OM.notSymbol
impliesSymbol    = newSymbol OM.impliesSymbol
equivalentSymbol = newSymbol OM.equivalentSymbol
andSymbol        = makeAssociative $ newSymbol OM.andSymbol
orSymbol         = makeAssociative $ newSymbol OM.orSymbol

-----------------------------------------------------------
--- Pretty-Printer

-- | Pretty printer for propositions
ppLogic :: Show a => Logic a -> String
ppLogic = ppLogicWith show asciiTuple

-- | Pretty printer with unicode characters
ppLogicUnicode :: Show a => Logic a -> String
ppLogicUnicode = ppLogicWith show unicodeTuple

ppLogicWith :: (a -> String) -> SymbolTuple -> Logic a -> String
ppLogicWith f (impl, equiv, conj, disj, neg, tr, fl) = rec1
 where
   rec1 p@(_ :&&: _) = recAnd p
   rec1 p@(_ :||: _) = recOr p
   rec1 (p :->: q)   = binop impl (rec2 p) (rec2 q)
   rec1 (p :<->: q)  = binop equiv (rec2 p) (rec2 q)
   rec1 p            = rec2 p

   recAnd (p :&&: q) = binop conj (rec2 p) (recAnd q)
   recAnd p          = rec2 p

   recOr (p :||: q) = binop disj (rec2 p) (recOr q)
   recOr p          = rec2 p

   rec2 (Not p) = neg ++ rec2 p
   rec2 p       = rec3 p

   -- atoms
   rec3 (Var x) = f x
   rec3 T       = tr
   rec3 F       = fl
   rec3 p       = pars (rec1 p)

   binop op x y = unwords [x, op, y]
   pars s = "(" ++ s ++ ")"

-----------------------------------------------------------
--- Ascii symbols

type SymbolTuple = (String, String, String, String, String, String, String)

asciiTuple :: SymbolTuple
asciiTuple = ("->", "<->", "/\\", "||", "~", "T", "F")

-----------------------------------------------------------
--- Unicode symbols

unicodeTuple :: SymbolTuple
unicodeTuple = (implUSym, equivUSym, andUSym, orUSym, notUSym, "T", "F")
 where
   implUSym  = "\8594"
   equivUSym = "\8596"
   andUSym   = "\8743"
   orUSym    = "\8744"
   notUSym   = "\172"