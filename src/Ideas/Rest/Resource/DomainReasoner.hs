{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.DomainReasoner where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
--import Servant.HTML.Lucid
import Ideas.Service.DomainReasoner
import Ideas.Utils.Prelude
import Control.Monad
--import Ideas.Rest.HTML.Page

data ResourceDomainReasoner = RDomainReasoner Links DomainReasoner

type GetDomainReasoner = Get '[JSON] ResourceDomainReasoner

instance ToJSON ResourceDomainReasoner where
   toJSON (RDomainReasoner _ dr) = String (pack (show (getId dr)))

instance ToSample ResourceDomainReasoner where
    toSamples _ = []