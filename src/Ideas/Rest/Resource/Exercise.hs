{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Exercise where

import Ideas.Common.Library
import Ideas.Utils.Prelude
--import Ideas.Rest.HTML.Page
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
--import Servant.HTML.Lucid

data ResourceExercises = RExercises Links [Some Exercise]

data ResourceExercise = forall a . RExercise Links (Exercise a)

type GetExercise  = Get '[JSON] ResourceExercise
type GetExercises = "exercises" :> Get '[JSON] ResourceExercises

instance ToJSON ResourceExercises where
   toJSON (RExercises links xs) = toJSON [ RExercise links x | Some x <- xs ]
   
instance ToJSON ResourceExercise where
   toJSON (RExercise _ ex) = String (pack (show (getId ex)))

instance ToSample ResourceExercises where
    toSamples _ = []
   
instance ToSample ResourceExercise where
    toSamples _ = []