{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest (restfulMain) where

import Data.IORef
import Data.Text (unpack, pack, Text)
import Servant
import Network.Wai.Handler.Warp (run)
import Ideas.Common.Library
import Ideas.Service.DomainReasoner
import Ideas.Service.State
import Ideas.Rest.Links
import Ideas.Rest.Resource.DomainReasoner
import Ideas.Rest.Resource.Exercise
import Ideas.Rest.Resource.Example
import Ideas.Rest.Resource.State
import Ideas.Rest.Resource.Derivation
import Ideas.Rest.Resource.Strategy
import Ideas.Rest.Resource.Rule
import Ideas.Rest.API
import Ideas.Rest.Resource.API
   
type ExerciseProxy a = Proxy (Capture "exerciseid" Id :> a)

links :: Links
links = Links 
   { linkTop        = showUri $ ideasLink topAPI
--   , linkExercises  = showUri $ ideasLink exercisesAPI
--   , linkAPI        = showUri $ ideasLink theAPI
--  , linkExercise   = makeLink exerciseAPI . getId
--  , linkExamples   = makeLink examplesAPI . getId
--   , linkAddExample = makeLink addExampleAPI . getId
--   , linkStrategy   = makeLink strategyAPI . getId
--   , linkRules      = makeLink rulesAPI . getId
--   , linkRule       = \ex r -> showUri $ ideasLink ruleAPI (getId ex) (getId r)
--   , linkState      = \st -> showUri $ ideasLink stateAPI (getId st) (Just (prettyPrinter (exercise st) (stateTerm st))) (Just (show (statePrefix st)))
--   , linkSolution   = \st -> showUri $ ideasLink solutionAPI (getId st) (Just (prettyPrinter (exercise st) (stateTerm st))) (Just (show (statePrefix st)))
   }
 where
   makeLink f  = showUri . ideasLink f
   ideasLink x = safeLink ideasAPI x
   showUri x   = pack ("/" ++ show x)
   
   topAPI = Proxy :: Proxy GetDomainReasoner
--   exercisesAPI = Proxy :: Proxy GetExercises
--   theAPI = Proxy :: Proxy GetAPI
   
--   exerciseAPI = Proxy :: ExerciseProxy GetExercise
--   examplesAPI = Proxy :: ExerciseProxy GetExamples
--   strategyAPI = Proxy :: ExerciseProxy GetStrategy
   
--   addExampleAPI = Proxy :: ExerciseProxy AddExample
   
--   rulesAPI = Proxy :: ExerciseProxy GetRules
--   ruleAPI  = Proxy :: ExerciseProxy GetRule
--   stateAPI = Proxy :: ExerciseProxy ("state" :> QueryParam "term" String :> QueryParam "prefix" String :> GetState)
--   solutionAPI = Proxy :: ExerciseProxy ("solution" :> QueryParam "term" String :> QueryParam "prefix" String :> GetDerivation)

-----------------------------------------------------------
-- Main

restfulMain :: DomainReasoner -> IO ()
restfulMain dr = do 
  ref <- newIORef dr
  run 8081 (serve ideasAPI (ideasServer links ref))

instance ToHttpApiData Id where
   toUrlPiece = pack . showId

instance FromHttpApiData Id where
   parseUrlPiece = Right . newId . unpack

instance FromHttpApiData Difficulty where
   parseUrlPiece t = 
      case readM (unpack t) of
         Just d  -> Right d
         Nothing -> Left "not a difficulty"

{-
 
 import Data.String (fromString)
 
data IH

instance Accept IH where
   contentType _ = fromString "text" // fromString "html"
   
instance MimeRender IH DomainReasoner where
  mimeRender _ dr = fromString $ MyHTML.showHTML $ MyHTML.htmlPage "Hello" $ MyHTML.h1 "world"
  
-}