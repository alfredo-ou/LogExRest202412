{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

module Domain.Algebra.Boolean
   ( -- * Boolean algebra (re-exported)
     BoolValue(..), Boolean(..)
   , ands, ors, implies, equivalent
     -- * CoBoolean (matching)
   , CoBoolean(..), conjunctions, disjunctions
     -- * Monoids monoid
   , DualMonoid(..), And(..), Or(..)
   ) where

import Control.Applicative
import Domain.Algebra.Group
import Ideas.Common.Classes
import Test.QuickCheck
import qualified Data.Semigroup as Sem

--------------------------------------------------------
-- CoBoolean (matching)

class BoolValue a => CoBoolean a where
   isAnd        :: a -> Maybe (a, a)
   isOr         :: a -> Maybe (a, a)
   isComplement :: a -> Maybe a

instance CoBoolean a => CoMonoid (And a) where
   isEmpty  = isTrue . fromAnd
   isAppend = fmap (mapBoth And) . isAnd . fromAnd

instance CoBoolean a => CoMonoidZero (And a) where
   isMonoidZero = isFalse . fromAnd

instance CoBoolean a => CoMonoid (Or a) where
   isEmpty  = isFalse . fromOr
   isAppend = fmap (mapBoth Or) . isOr . fromOr

instance CoBoolean a => CoMonoidZero (Or a) where
   isMonoidZero = isTrue . fromOr

conjunctions :: CoBoolean a => a -> [a]
conjunctions = map fromAnd . associativeList . And

disjunctions :: CoBoolean a => a -> [a]
disjunctions = map fromOr . associativeList . Or

--------------------------------------------------------
-- Dual monoid for a monoid (and for or, and vice versa)

class MonoidZero a => DualMonoid a where
   (><)      :: a -> a -> a
   dualCompl :: a -> a

--------------------------------------------------------
-- And monoid

newtype And a = And {fromAnd :: a}
   deriving (Show, Eq, Ord, Arbitrary, CoArbitrary)

instance Functor And where -- could be derived
   fmap f = And . f . fromAnd

instance Applicative And where
   pure            = And
   And f <*> And a = And (f a)

instance Boolean a => Sem.Semigroup (And a) where
   (<>) = liftA2 (<&&>)

instance Boolean a => Monoid (And a) where
   mempty  = pure true
   mappend = (Sem.<>)

instance Boolean a => MonoidZero (And a) where
   mzero = pure false

instance Boolean a => DualMonoid (And a) where
   (><)      = liftA2 (<||>)
   dualCompl = liftA complement

--------------------------------------------------------
-- Or monoid

newtype Or a  = Or {fromOr :: a}
   deriving (Show, Eq, Ord, Arbitrary, CoArbitrary)

instance Functor Or where -- could be derived
   fmap f = Or . f . fromOr

instance Applicative Or where
   pure          = Or
   Or f <*> Or a = Or (f a)

instance Boolean a => Sem.Semigroup (Or a) where
   (<>) = liftA2 (<||>)

instance Boolean a => Monoid (Or a) where
   mempty  = pure false
   mappend = (Sem.<>)

instance Boolean a => MonoidZero (Or a) where
   mzero = pure true

instance Boolean a => DualMonoid (Or a) where
   (><)      = liftA2 (<&&>)
   dualCompl = liftA complement