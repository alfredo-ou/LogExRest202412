{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Example where

import Control.Monad
import Ideas.Common.Library
import Ideas.Common.Examples
import Data.Aeson.Types
import Data.Function
import Data.List
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
--import Ideas.Rest.HTML.Page
import Servant.Docs
import Servant
--import Servant.HTML.Lucid
import Ideas.Service.State

data ResourceExamples = forall a . RExamples Links (Exercise a) (Examples a)

data ResourceExample = forall a . RExample Links (Exercise a) (Maybe Difficulty) a

type GetExamples = "examples" :> Get '[JSON] ResourceExamples

type GetExamplesDifficulty = "examples" :> Capture "difficulty" Difficulty :> Get '[JSON] ResourceExamples

--instance ToJSON ResourceExamples where
--    toJSON (RExamples links ex xs) = toJSON [ RExample links ex dif a | (dif, a) <- xs ]

instance ToJSON ResourceExamples where
    toJSON (RExamples links ex exs) =
        let examplesList = [ RExample links ex md a | (md, a) <- allExamples exs ]
        in toJSON examplesList

instance ToJSON ResourceExample where
   toJSON (RExample _ ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))

instance ToSample ResourceExamples where
    toSamples _ = []
   
instance ToSample ResourceExample where
    toSamples _ = []
    
type AddExample = "add-example" :> Get '[JSON] AddExampleForm

data AddExampleForm = forall a . AddExampleForm Links (Exercise a)

instance ToJSON AddExampleForm where
   toJSON _ = Null

instance ToSample AddExampleForm where
   toSamples _ = []