{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.KnowledgeComponent where

import Ideas.Common.Library
--import Ideas.Rest.HTML.Page
import Ideas.Rest.Links
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Servant.Docs
import Servant hiding (Context)
--import Servant.HTML.Lucid


data KnowledgeComponents = forall a . RRules Links (Exercise a) [Rule (Context a)]

data KnowledgeComponent = forall a . RRule Links (Exercise a) (Rule (Context a))

type GetRules = "rules" :> Get '[JSON] KnowledgeComponents

type GetRule = "rules" :> Capture "ruleid" Id :> Get '[JSON] KnowledgeComponent

instance ToJSON KnowledgeComponents where
   toJSON (RRules links ex rs) = 
      toJSON [ RRule links ex r | r <- rs ]
   
instance ToJSON KnowledgeComponent where
   toJSON (RRule _ _ r) = String (pack (show (getId r)))

instance ToSample KnowledgeComponents where
    toSamples _ = []

instance ToSample KnowledgeComponent where
    toSamples _ = []
