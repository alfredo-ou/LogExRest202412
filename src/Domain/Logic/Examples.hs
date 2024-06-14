-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  josje.lodder@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-- A set of example proofs
--
-----------------------------------------------------------------------------

module Domain.Logic.Examples
   ( dnfExamples, cnfExamples, exampleProofs
   ) where

import Domain.Logic.Formula
import Ideas.Common.Exercise
import Ideas.Utils.Prelude (ShowString(..))

dnfExamples :: Examples SLogic
dnfExamples = examplesWithDifficulty
   [ (Easy, Not(q :->: r) :||: q :||: r)
   , (Easy, Not(p:<->: p))  --extra voor Marianne
   , (Easy,(p :||:r):&&: (q:||:p)) --extra voor Marianne
   , (Easy, (T :&&:q) :->: (r :->:p)) --extra voor Marianne
   , (Easy,Not(Not q :->: Not r)) --extra voor Marianne
   , (Medium, (Not q :&&: Not (p :->: q)) :->: p)
   , (Medium, (q :||: Not r) :&&: (q :||: p) :&&: Not q)
   , (Medium, Not p :<->: (p :&&: q))
   , (Medium, ((q :->: r):&&:r) :->: r) --extra voor Marianne
   , (Medium, ((q:||:p):<->:(q:||:p)) :->:((q:||:p)  :||:r))  --extra voor Marianne
   , (Difficult, (p :||: q) :&&: (r :<->: p))
   , (Difficult, ((q :->: s) :&&: (s :<->: r)) :&&: Not(s :||: r)) --extra voor Marianne
   , (Difficult, r :<->: ((r :&&: q) :||: Not s)) --extra voor Marianne
   , (Difficult, Not (q :->: s) :<->: Not (p :->: s) ) --extra voor Marianne
   , (Difficult, Not( Not p :<->: (p :<->: s))) --extra voor Marianne
   , (Medium, (p :->: q):<->: p ) -- pretest Marianne
   , (Medium, (p :||: q :||: r) :&&: (r :||: Not p)) -- posttest Marianne
   ]
   -- ((q :&&: r) :->: (q :->: r)) :->: (r :&&: (q :->: p))
   -- (q :&&: p) :<->: (q :&&: r)
   -- Not ((p :&&: q) :<->: (Not r :||: q))
 where
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   s = Var (ShowString "s")

cnfExamples :: Examples SLogic
cnfExamples = examplesWithDifficulty
   [ (Easy, Not ((q :->: r) :->: Not q))
   , (Easy, (Not q :&&: Not (p :->: q)) :->: p)
   , (Easy, Not ((p:&&: q):->:(q:||:r))) --extra voor Marianne
   , (Easy, (q :->: q) :->:  Not q) --extra voor Marianne
   , (Easy, (q :<->: F) :&&: q) --extra voor Marianne
   , (Medium, p :<->: (p :&&: q))     
   , (Medium, ((q :||: p) :->: (q :->: p)) :->: (r :&&: q :&&: p))
   , (Medium, Not(r :||: q) :&&: (Not p:||: (p :||:r))) --extra voor Marianne
   , (Medium, (p :||: (p :<->: r)) :&&: r) --extra voor Marianne
   , (Medium, Not((r :||: p) :&&: (p :->: r))) --extra voor Marianne
   , (Difficult, (p :&&: q) :||: (p :<->: r))
   , (Difficult, (Not r :->: Not s) :->: Not (q :&&: p)) --extra voor Marianne
   , (Difficult, s :->: ((p :->: s) :->: (r :<->: q))) --extra voor Marianne
   , (Difficult, Not((p :||: s) :<->: (s :&&: q))) --extra voor Marianne
   , (Difficult, Not(q :&&: s) :&&: ((p :<->: q) :->: (r :||: s))) --extra voor Marianne
   , (Medium, (p :<->: q) :->: p)  -- pretestMarianne
   , (Medium, ((p :&&: Not(Not p :||:q)) :||:(p :&&: q)) :->: p) --posttest Marianne
   ]
   -- Not (q :->: r) :||: q :||: r
   -- ((q :||: p) :&&: (p :||: r)) :||: Not (q :||: r)
   -- (q :&&: p) :<->: (q :&&: r)
 where
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   s = Var (ShowString "s")

exampleProofs :: Examples (SLogic, SLogic)
exampleProofs = examplesWithDifficulty


   [ {- 16 -} easy      (Not(p :&&: q) :||: (s :||: Not r), (p :&&: q) :->: (r :->: s))  
   , {- 19 -} easy      (p :&&: q, Not(p :->: Not q))
   , {- 15 -} easy      (q :&&: p, p :&&: (q :||: q))
   , {- 17 -} easy      (Not(Not p :&&: Not(q :||: r)),  p :||: (q :||: r))
   , {- 18 -} easy      (Not (p :&&: (q :||: r)), Not p :||: (Not q :&&: Not r))
   , {- 23 -} easy      (p :<->: q, Not p :<->: Not q)
   ,          easy      (Not p :||: (q :&&: r), (p :->: q) :&&: (p :->: r)) -- nieuw distributie, standaarduitwerking niet optimaal
   ,          easy      ((p :&&:q) :||:Not q :||:p, q :->: p)  --nieuw absorptie
   ,          easy      (p :&&: Not(Not p :&&: q), p)  --nieuw absorptie
   ,          easy      ((Not p :||: q) :&&: Not r, Not (p :||: r ):||: (q :&&: Not r)) 
   , {-  6 -} easy      ((p :&&: q) :->: p, T)
   , {-  1 -} easy      (Not(p :||: (Not p :&&: q)), Not(p :||: q))
   , {-  2 -} easy      ((p :->: q):||: Not p, (p :->: q) :||: q)
   , {-  7 -} easy      ((p :->: q) :||: (q :->: p), T)
   , {-  4 -} medium    (Not(p :||: Not(p :||: Not q)), Not(p :||: q)) --medium
   , {- 13 -} medium    (Not((p :->:q) :->: (p:&&:q)), (p :->: q) :&&: (Not p :||: Not q))
   , {- 14 -} medium    (Not((p :<->: q) :->: (p :||: (p :<->: q))), F)
   , {- 21 -} medium    ((p :->: q) :->: Not p, p :->: (q :->: Not p))
   , {- 22 -} medium    ((Not q :&&: p) :->: p, (Not q :<->: q) :->: p)
   , {- 25 -} medium    (p :<->: (p :&&: q), p :->: q)
   , {- 26 -} medium    (p :<->: (p :->: q), p :&&: q)
   , {- 27 -} medium    ((p :->: q ) :&&: (r :->: q), (p :||: r) :->: q)
   , {- 12 -} medium    ((p :->: q):->: (p :->: s), (Not q :->: Not p) :->: (Not s :->: Not p))
   , {- 31 -} medium    (p :&&: (q :||: s), (q :&&: Not s :&&: p) :||: (p :&&: s))  
   , {-  9 -} medium    ((p :->: Not q):->:q, (s :||:(s :->:(q :||: p))) :&&: q)
   ,          medium    (p :<->:(q :&&:p),p:->:q)
   , {-  8 -} difficult ((q :->: (Not p :->: q)) :->: p, Not p :->: (q :&&: ((p :&&: q) :&&: q))) 
   , {- 10 -} difficult (p :->: (q :->: r), (p :->: q) :->: (p :->:r))
   , {- 11 -} difficult (Not((p :->: q) :->: Not(q :->: p)), p :<->: q)
   , {-  3 -} difficult ((p :&&: Not q):||:(q :&&: Not p), (p :||:q):&&:Not(p :&&: q))
   , {- 28 -} difficult ((p :&&: (q :&&: r)) :||: (Not p :&&: q), (Not p :&&: (q :&&: Not r)) :||: ( q :&&: r))
   , {-  5 -} difficult (p :<->: q, (p :->: q) :&&: (q :->: p))
   , {- 20 -} difficult (p :<->: (q :<->: p),q)
   , {- 24 -} difficult ((p :->: q) :<->: (p :->: r), (p :->: (q :&&: r)) :||: Not(p :->: (q :||: r))) 
   , {- 29 -} difficult (p :||: (q :&&: r), ( p :&&: Not q) :||: ( p :&&: Not r):||: ( q :&&: r))
   , {- 30 -} difficult ((p :&&: q) :||: (Not q :&&: r), ( p :&&: r) :||: ( p :&&: q :&&: Not r):||: (Not p :&&: Not q :&&: r))
   , {- 31 -} difficult (Not((q :<->: p) :||: (r :->: p)),Not p :&&: r :&&: (q :||: p))
   , {- 32 -} difficult (p :&&:(q:||:r),p :&&:((p :&&: q) :||:r))
   , {- 32 -} difficult (Not(p :->: Not(Not q :->: r)),p :&&: ((p :&&: q) :||: r))
   , {- test -} difficult (p :&&: (q :||: r),p :&&: ((p:&&: q) :||: r)  )
   , {- test -} difficult ((p :&&: q :&&: p) :||: (p :&&: q :&&: Not p) :||: (Not p :&&: q), q)
   , {- 28var1 -} difficult ((p :&&: (q :&&: r)) :||: (Not p :&&: q), (q :&&: (Not p :&&: Not r)) :||: ( q :&&: r))
   , {- 28var2 -} difficult ((q :&&: (p :&&: r)) :||: (q :&&: Not p), (q :&&: (Not p :&&: Not r)) :||: ( q :&&: r))
 --  , {- test -}  difficult  ((r :&&: p :&&: q ):||: (Not q :&&: r), (p:&&: r):||:(Not q :&&: r))
 --  , {- test -}  difficult  ((r :&&: p :&&: q ):||: (Not q :&&: r), (p:||:Not q) :&&: r)
 --  , {- test -}  difficult  ((p:&&: r):||:(Not q :&&: r),(r :&&: p :&&: q ):||: (Not q :&&: r))
 --  , {- test -}  difficult  (( p :&&: q :&&: r):||: (Not q :&&: r), (p:&&: r):||:(Not q :&&: r))
 --  , {- test -}  difficult  ((r :&&: p :&&: q ):||: (Not q :&&: r),  ((p:&&: q):||:Not q) :&&: r)
  -- , {- test -}  difficult  (( p :&&: q :&&: r):||: (Not q :&&: r), (r:&&: p):||:(Not q :&&: r))
   ]
 where
   easy      x = (Easy, x)
   medium    x = (Medium, x)
   difficult x = (Difficult, x)

   p = Var (ShowString "p")
   q = Var (ShowString "q")
   s = Var (ShowString "s")
   r = Var (ShowString "r")

{-
makeTestCases :: IO ()
makeTestCases = zipWithM_ makeTestCase [0..] exampleProofs

makeTestCase :: Int -> (SLogic, SLogic) -> IO ()
makeTestCase n (p, q) =
   writeFile ("proof" ++ show n ++ ".json")
      (json $ show p ++ " == " ++ show q)

json :: String -> String
json s = unlines
   [ "{ \"method\" : \"derivation\""
   , ", \"params\" : [[\"logic.proof\", \"[]\", " ++ show s ++ ", \"\"]]"
   , ", \"id\"     : 42"
   , "}"
   ] -}
