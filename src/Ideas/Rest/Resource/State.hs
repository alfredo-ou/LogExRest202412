{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.State where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
--import Ideas.Rest.HTML.Page
import Ideas.Service.State
import Ideas.Service.BasicServices
import Servant.Docs
import Servant
--import Servant.HTML.Lucid

data ResourceState = forall a . RState Links (State a)

type GetState = Get '[JSON] ResourceState

instance ToJSON ResourceState where
   toJSON (RState _ _) = String (pack "resource state")

instance ToSample ResourceState where
    toSamples _ = []
