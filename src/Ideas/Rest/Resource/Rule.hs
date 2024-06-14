{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Rule where

import Ideas.Common.Library
--import Ideas.Rest.HTML.Page
import Ideas.Rest.Links
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Servant.Docs
import Servant hiding (Context)
--import Servant.HTML.Lucid

data ResourceRules = forall a . RRules Links (Exercise a) [Rule (Context a)]

data ResourceRule = forall a . RRule Links (Exercise a) (Rule (Context a))

type GetRules = "rules" :> Get '[JSON] ResourceRules

type GetRule = "rules" :> Capture "ruleid" Id :> Get '[JSON] ResourceRule

instance ToJSON ResourceRules where
   toJSON (RRules links ex rs) = 
      toJSON [ RRule links ex r | r <- rs ]
   
instance ToJSON ResourceRule where
   toJSON (RRule _ _ r) = String (pack (show (getId r)))

instance ToSample ResourceRules where
    toSamples _ = []

instance ToSample ResourceRule where
    toSamples _ = []
