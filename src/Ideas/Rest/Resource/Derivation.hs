{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Derivation where

import Control.Monad
import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
--import Ideas.Rest.HTML.Page
import Ideas.Service.State
import Ideas.Service.BasicServices
import Servant.Docs
import Servant hiding (Context)
--import Servant.HTML.Lucid

data ResourceDerivation = forall a . RDerivation Links (Exercise a) (Derivation (Rule (Context a), Environment) (Context a))

type GetDerivation = Get '[JSON] ResourceDerivation

instance ToJSON ResourceDerivation where
   toJSON (RDerivation _ _ _) = String (pack "derivation")

instance ToSample ResourceDerivation where
    toSamples _ = []