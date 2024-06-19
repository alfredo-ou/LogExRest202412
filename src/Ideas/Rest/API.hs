{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.API where

import Control.Monad.IO.Class as MIO
import Data.IORef
import Servant
import Ideas.Common.Library
import Ideas.Service.DomainReasoner
import Ideas.Utils.Prelude
import Ideas.Service.State
import Ideas.Service.BasicServices (solution)
import Ideas.Rest.Links
import Ideas.Rest.Resource.Exercise
import Ideas.Rest.Resource.Example
import Ideas.Rest.Resource.State
import Ideas.Rest.Resource.Strategy
import Ideas.Rest.Resource.Rule
import Ideas.Rest.Resource.DomainReasoner
import Ideas.Rest.Resource.API
import Ideas.Rest.Resource.Derivation
import Servant.Docs
import Data.Aeson.Types
--import Servant.HTML.Lucid
--import Ideas.Rest.HTML.Docs
import Lucid
--import Ideas.Rest.HTML.Page
import Data.Text (unpack)

-----------------------------------------------------------
-- API

type IdeasAPI = 
        GetDomainReasoner
--   :<|> GetExercises
--   :<|> GetAPI
--   :<|> ExerciseAPI
   
-- type ExerciseAPI = Capture "exerciseid" Id :>
--   (    GetExercise
--   :<|> GetExamples
--   :<|> GetExamplesDifficulty
--   :<|> AddExample
--   :<|> "examples" :>  ReqBody '[JSON] NewExample :> PostNoContent '[JSON] ()
--   :<|> GetStrategy
--   :<|> GetRules
--   :<|> GetRule
--   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> GetState
--   :<|> "solution" :> QueryParam "term" String :> QueryParam "prefix" String :> GetDerivation
--   )

-----------------------------------------------------------
-- Server

ideasAPI :: Proxy IdeasAPI
ideasAPI = Proxy

instance ToParam (QueryParam "prefix" String) where
    toParam _ =
       DocQueryParam "prefix" [] "strategy prefix" Normal

instance ToParam (QueryParam "term" String) where
    toParam _ =
       DocQueryParam "term" [] "current term" Normal

instance ToCapture (Capture "exerciseid" Id) where
    toCapture _ = 
       DocCapture "exerciseid" "exercise identitifer" 
       
instance ToCapture (Capture "ruleid" Id) where
    toCapture _ = 
       DocCapture "ruleid" "rule identitifer" 

instance ToCapture (Capture "difficulty" Difficulty) where
    toCapture _ = 
       DocCapture "difficulty" "difficulty" 


ideasServer :: Links -> IORef DomainReasoner -> Server IdeasAPI
ideasServer links ref =
   withDomainReasoner ref (RDomainReasoner links)
-- :<|>
--   withDomainReasoner ref (RExercises links . exercises)
-- :<|>
--   return (ResourceAPI links $ docs ideasAPI)
-- :<|>
--   exerciseServer links ref

-- exerciseServer :: Links -> IORef DomainReasoner -> Server ExerciseAPI
-- exerciseServer links ref s =
--   withExercise ref s (RExercise links)
-- :<|>
--   withExercise ref s (\ex -> RExamples links ex (examples ex))
-- :<|>
--   (\dif -> withExercise ref s (\ex -> RExamples links ex (filter ((==dif) . fst) (examples ex))))
-- :<|>
--  withExercise ref s (\ex -> AddExampleForm links ex)
-- :<|> (\(NewExample txt dif) -> do
--  dr <- liftIO (readIORef ref)
--  Some ex <- findExercise dr s
--  case parser ex txt of
--     Left msg -> fail msg
--     Right a  -> do
--        liftIO (writeIORef ref dr {exercises = map (\(Some x) -> if getId x == getId ex then Some (ex {examples = (dif, a) : examples ex}) else Some x) (exercises dr)})
--        return ())
-- :<|>
--   withExercise ref s (RStrategy . strategy)
-- :<|>
--   withExercise ref s (\ex -> RRules links ex (ruleset ex))
-- :<|>
--   (\n -> withExerciseM ref s (\ex -> do
--      r <- getRule ex n
--      return $ RRule links ex r))
-- :<|> (\mt mp -> do
--   Some ex <- someExercise ref s
--   case maybe (Left "no term") (parser ex) mt of
--      Left msg -> error msg
--      Right a  ->
--         case maybe Nothing readPaths mp of
--            Just ps -> return (RState links (makeState ex (replayPaths ps (strategy ex) (inContext ex a)) (inContext ex a)))
--            Nothing -> return (RState links (emptyState ex a)))
{--
 :<|> (\mt mp -> do
   Some ex <- someExercise ref s
   case maybe (Left "no term") (parser ex) mt of 
      Left msg -> error msg
      Right a  -> 
         case maybe Nothing readPaths mp of
            Just ps -> 
               let st = makeState ex (replayPaths ps (strategy ex) (inContext ex a)) (inContext ex a)
               in case solution Nothing st of
                     Left msg -> error msg 
                     Right d  -> return (RDerivation links ex d)
            Nothing -> 
               let st = emptyState ex a 
               in case solution Nothing st of
                     Left msg -> error msg 
                     Right d  -> return (RDerivation links ex d))
-}

--someExercise :: IORef DomainReasoner -> Id -> Either String (Some Exercise)
someExercise :: IORef DomainReasoner -> Id -> Either String (Some Exercise)
someExercise ref s = do
   dr <- liftIO (readIORef ref)
   findExercise dr s

withDomainReasoner :: IORef DomainReasoner -> (DomainReasoner -> a) -> Either String a
withDomainReasoner ref f = do 
   dr <- liftIO (readIORef ref)
   return (f dr)
{---
-- withExerciseM :: MonadIO m => IORef DomainReasoner -> Id -> (forall a . Exercise a -> m b) -> m b
withExerciseM :: IORef DomainReasoner -> Id -> (forall a . Exercise a -> Either String b) -> Either String b
withExerciseM ref s f = do
   Some ex <- someExercise ref s
   f ex

--withExercise :: MonadIO m => IORef DomainReasoner -> Id -> (forall a . Exercise a -> b) -> m b
withExercise :: IORef DomainReasoner -> Id -> (forall a . Exercise a -> b) -> Either String b
withExercise ref s f = do
   Some ex <- someExercise ref s
   return (f ex) 
-}

-- instance ToSample Char

instance ToSample Difficulty where
   toSamples _ = []
   
instance ToJSON Difficulty where
   toJSON = toJSON . show
 
instance FromJSON Difficulty where
   parseJSON (String txt) =
      case readM (unpack txt) of
         Just dif -> return dif
         Nothing  -> fail "difficulty not recognized" 
   parseJSON _ = fail "difficulty must be a string"
   
data NewExample = NewExample String Difficulty

instance ToJSON NewExample where
   toJSON (NewExample s dif) = 
      object ["expr" .= s, "difficulty" .= dif]

instance ToSample NewExample where
   toSamples _ = []
   
instance FromJSON NewExample where
   parseJSON (Object xs) = 
      NewExample <$> xs .: "expr" <*> xs .: "difficulty"
   parseJSON _ = fail "new example must be an object"