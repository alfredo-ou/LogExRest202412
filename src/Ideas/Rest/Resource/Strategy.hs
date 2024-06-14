{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Strategy where

import Ideas.Common.Library
import Data.Aeson.Types
import Data.Text (pack)
import Servant.Docs
import Servant

data ResourceStrategy = forall a . RStrategy (LabeledStrategy a)

type GetStrategy = "strategy" :> Get '[JSON] ResourceStrategy

instance ToJSON ResourceStrategy where
   toJSON (RStrategy s) = String (pack (show s))
   
instance ToSample ResourceStrategy where
    toSamples _ = []