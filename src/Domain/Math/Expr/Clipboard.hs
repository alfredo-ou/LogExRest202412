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
-- Support for a clipboard, on which expressions can be placed. The clipboard
-- is part of the environment (terms that are placed in a context)
--
-----------------------------------------------------------------------------

module Domain.Math.Expr.Clipboard
   ( -- * Data type
     Clipboard
     -- * Interface
   , addToClipboard, removeClipboard, lookupClipboard
     -- * Generalized interface
   , addToClipboardG, lookupClipboardG
   ) where

import Data.Maybe
import Data.Typeable
import Domain.Math.Data.Relation
import Domain.Math.Expr.Data
import Domain.Math.Expr.Parser
import Ideas.Common.Library
import qualified Data.Map as M

---------------------------------------------------------------------
-- Clipboard variable

newtype Clipboard = C {unC :: M.Map String Expr}
   deriving Typeable

instance Show Clipboard where
   show = show . toExpr

instance Read Clipboard where
   readsPrec _ txt = 
      case parseExpr txt of
         Left _ -> []
         Right expr ->
            case fromExpr expr of
               Just clip -> [(clip, "")]
               Nothing   -> []

instance IsTerm Clipboard where
   toTerm =
      let f (s, a) = Var s :==: a
      in toTerm . map f . M.toList . unC
   termDecoder =
      let f (x :==: a) = (\k -> (k, a)) <$> getVariable x
      in C . M.fromList . mapMaybe f <$> termDecoder

instance Reference Clipboard

clipboard :: Ref Clipboard
clipboard = makeRef "clipboard"

getClipboard :: Context a -> Clipboard
getClipboard = fromMaybe (C M.empty) . (clipboard ?)

changeClipboard :: (Clipboard -> Clipboard) -> Context a -> Context a
changeClipboard f c = insertRef clipboard (f (getClipboard c)) c

---------------------------------------------------------------------
-- Interface to work with clipboard

addToClipboard :: String -> Expr -> Context a -> Context a
addToClipboard = addToClipboardG

lookupClipboard :: String -> Context b -> Maybe Expr
lookupClipboard = lookupClipboardG

removeClipboard :: String -> Context a -> Context a
removeClipboard s = changeClipboard (C . M.delete s . unC)

---------------------------------------------------------------------
-- Generalized interface to work with clipboard

addToClipboardG :: IsTerm a => String -> a -> Context b -> Context b
addToClipboardG s a = changeClipboard (C . M.insert s (toExpr a) . unC)

lookupClipboardG :: IsTerm a => String -> Context b -> Maybe a
lookupClipboardG s c = clipboard ? c >>= M.lookup s . unC >>= fromExpr