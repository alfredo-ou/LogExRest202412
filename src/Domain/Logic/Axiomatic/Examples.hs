module Domain.Logic.Axiomatic.Examples 
   ( exampleList, mmExampleList, wendyList, lemmaList, firstExamplesList
   ) where

import Ideas.Utils.Prelude
import Ideas.Common.Library
import Domain.Logic.Formula
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Lemma

wendyList :: [(Difficulty, Statement, Lemmas)]
wendyList = map (\(d, st, l) -> (d, st, [lemma l]))
   [
      (Easy, [Not (Not p)] |- Not q :->: p, [] |- Not (Not p) :->: p),
      -- (Easy, [p, p :->: q] |- q, ([] |- Not (Not p) :->: p)),
      (Medium, [p] |- Not p :->: Not q, [] |- (q :->: p) :->: (Not p :->: Not q)),
  --    (Medium, [p, Not p] |- Not q, [] |- (q :->: p) :->: (Not p :->: Not q)),
      -- (Medium, [p, Not p] |- Not q, ([] |- (q :->: Not p) :->: ( p :->: Not q))),
      (Medium, [] |- p :->: (Not p :->: q), [] |- Not p :->: (p :->: q)),
      (Medium, [Not (Not p) :->: q] |- (r :->: p) :->: (r :->: q), [] |- p :->: Not (Not p)),
      (Medium, [p :->: Not (Not q)] |- (r :->: p) :->: (r :->: q), [] |- Not (Not q) :->: q)
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   
   
lemmaList :: [(Difficulty, Statement, Lemmas)]
lemmaList =  map (\(d, st, l) -> (d, st, [lemma l]))
   [
      (Medium, [] |- Not (Not p) :->: p, [Not (Not p)] |- Not p :->: Not (Not (Not p))), -- logic course
   --   (Easy, [] |- p :->: ( q :->: q), [p] |- q :->: q), --23 opgave 5
   --   (Medium, []|- p :->: ((p :->: q) :->: q), [] |- (p :->: q) :->: (p :->: q)), --38 opgave 9
--      (Medium, [ p :->: (q :->:(q :->: r))] |- p :->: (q :->: r), [] |- (q :->: q)), --47 lemma niet nodig
--      (Medium, []|-(p :->: (p :->: q)):->: (p:->:q), []|- p :->: ((p :->: q) :->: q)), --50 lemma niet nodig
 --     (Medium, [p :->: (q :->: (r :->: s)), p :->: (q :->: (s:->: t)) ]|- p :->: (q :->: (r :->: t)), Just $ [] |- (s :->: t) :->: ((r :->: s):->:(r:->:t))), --64
  --    (Medium, [p :->:(q :->: r)] |- p:->: ((r :->: s) :->: (q :->: s)), [] |- p :->: ( s :->: s)),  -- 72
 --     (Medium, [p :->:(q :->: r)] |- p:->: ((r :->: s) :->: (q :->: s)), [] |- t :->: t),  -- 72 met dummy lemma
 --     (Medium, []|-(p:->:q) :->: ((q :->: r):->: (p:->:r)), [] |- (p :->: q) :->: (p :->: q)), --73
      (Medium, []|-(s:->: (p:->:q)) :->: ((s:->: (q :->: r)):->: (s:->: (p:->:r))), []|-(p:->:q) :->: ((q :->: r):->: (p:->:r))), --74
 --     (Medium, [p :->: (q :->: (r :->: s)) ]|- p :->: (r :->: (q :->: s)), []|- r :->: ((r :->: s) :->: s)), --75
      (Medium, [] |- (p :->: ( q :->: r)) :->: (q :->: ( p :->: r)), [] |- (p :->: ( q :->: r)) :->: (p :->: ( q :->: r))),  -- 79      
    --  (Medium, [s:->:(t:->:(p :->: ( q :->: r)))] |-s:->: (t :->: (q :->: ( p :->: r))), Just $  [] |- (p :->: ( q :->: r)) :->: (q :->: ( p :->: r))),  -- 80
  --    (Medium, [] |- ((p :->:q):->: (p :->: r)):->:((q :->:p):->: (q :->: r)), [] |- ((p :->:q):->: (p :->: r)):->:(q :->: (p :->: r))), --99
 --     (Medium, [] |- Not p :->: ( p :->: q), [] |- Not p :->: Not p), --103 zonder lemma?
      (Medium, [] |- p :->: ( Not p :->: q), [] |- Not p :->: ( p :->: q)), --104
      (Difficult, [] |- (Not p :->: p) :->: p, [] |- Not p :->: ( p :->: Not (Not p :->: p))), --105
   --   (Medium, [] |- (Not p :->: p) :->: p,  [] |- t :->: t),  -- 105 met dummy lemma
   --   (Medium, [ p :->: ( Not q :->: q)] |- p :->: q, [] |-  (Not q :->: q) :->: q), --106 opgave 10
      (Difficult, [] |- Not (Not p) :->: p , [] |- Not (Not p) :->: (Not p :->: p)), --107
      (Medium, [p :->: Not (Not q)]  |- p:->: q , [] |- Not (Not q) :->: q), --108
      (Difficult, [p :->:(q :->: Not r)] |- p:->: (r :->: Not q) , [] |- Not (Not q) :->: q),  -- 110     
      (Easy, [Not (Not p)] |- p , [] |- Not (Not p) :->: p), --109
      (Difficult, [] |- p :->: (q :->:Not (p:->: Not q)), [] |- p :->: ((p :->: Not q) :->: Not q)),  -- 140   
      (Medium, [p :->: q, p :->: r] |- (p :->:Not (q:->: Not r)),  [] |- q :->: (r :->:Not (q:->: Not r))),  -- 142 
      (Medium, [Not (p:->: Not q) :->: r]  |- p :->:(q :->: r) ,  [] |- p :->: (q :->:Not (p:->: Not q))), --144
      (Medium, []  |- Not(p :->: q) :->: (q :->: p) , [] |-  Not(p :->: q) :->: p) , --149
      --       (Medium, []  |- ((p :->: q) :->: q) :->: ((q :->: p) :->: p) ,[ [] |-  (p:->:q) :->: ((q :->: p):->: ((p:->:q) :->:p)),[] |-  ((p :->: q) :->: p):->: p] ) , --176, twee lemma's
      
      (Medium, [p :->: Not (Not q)] |- (r :->: p) :->: (r :->: q),  [] |- Not (Not q) :->: q),
   --   (Medium, [Not (Not p)] |- Not p :->: Not(Not(Not p)), [] |- Not (Not p) :->: p), -- zelftoets leh 4 2ii, dubbel
      (Medium, [] |- Not (Not p) :->: p, [Not(Not p)] |- Not p :->:Not(Not (Not p) )),   -- zelftoets leh 4 2iii
      (Medium, [] |- ((p :->:q):->: (Not q :->: Not p)), [] |- (p :->:q):->: (Not (Not p) :->: Not(Not q)))  -- opg 4.3.5
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")   
   s = Var (ShowString "s")
--   t = Var (ShowString "t")   

exampleList :: [(Difficulty, Statement, Lemmas)]
exampleList = 
   [ -- difficult $ [] |- Not( ((p :->: (q :->:r)) :->: (Not (p :->: Not q) :->: r)) :->: Not ((Not (p :->: Not q) :->: r) :->: (p :->: (q :->:r))))
 --    ,  difficult $ [] |-  ((p :->: (q :->:r)) :->: (Not (p :->: Not q) :->: r))
 --    , difficult $ [r :->: Not (p :->: p) ]|- r :->: q 
--   , difficult $ [Not (p :->: Not q) :->: r ]|- p :->: (q :->:r)
--   , difficult $ [] |- Not((p :->: p):->:Not (q :->: q))
--    medium $ [p :->: q] |- (r :->: p) :->: (r :->: q) opgave 6
    medium $ [(p :->: q) :->: (p :->: r)] |-  p :->: (q :->: r)
--   , easy $ [p, p :->: q] |- q opgave 1
--   , easy $ [Not q :->: Not p] |- p :->: q opgave 2
--   , easy $ [] |- p :->: ((p :->: q) :->: q)  opgave 3
--   , medium $ [Not p]|- p :->: q opgave 7
   , medium $ [p, Not p] |- q
--   , medium $ [(p :->: q) :->:r, q]|- r opgave 8
   , medium $ [(p :->: q) :->: Not p] |- q :->: Not p
   , medium $ [Not (p :->: q), q] |- r
   --medium $  , [Not (Not p) :->:  Not q, r :->: q ]|- r :->: Not p
--   , difficult $ [Not (p :->: q)] |- p
--   , difficult $ [Not (p :->: q)] |- Not q
   , medium $ []|- ((p :->: q) :->: (q :->: p)):->: (q :->: p)
   , medium $ [p, Not q :->: (p :->: Not r)] |-  r :->: q
   , medium $ [p :->: r, p :->: (Not q :->: Not r)] |- p :->: q
 --  , difficult $ []|- Not (Not (Not q)) :->: Not q
   , easy $ [p, q] |- r :->: q
--   , difficult $ [p :->: q] |- (r :->: p) :->: (Not (Not r) :->: q)
 --  , difficult $ [p :->: (Not q :->: q)] |- p :->: q
 --  , difficult $ [p :->: Not q, r :->: q] |- r :->: Not p
--   , difficult $ [Not (Not p) :->: (Not q :->: Not (Not q))] |- p :->: q 
 --  , difficult $ [] |- ((p :->: q) :->: p) :->: p
--   , difficult $ [p :->: Not p] |-  Not p    
 --  , difficult $ [Not q, p :->: q ] |-  Not p
--   , difficult $ [p :->:  q, r :->: Not q] |- r :->: Not p
 --  , difficult $ [p :->:  q, Not p :->: q] |- q
 --  , difficult $ [Not p :->:  q, Not p :->: Not q] |- p
--   , difficult $ [p :->: q, p:->: Not q] |- Not p
--   , difficult $ [] |- Not (p :->: q):->: Not q
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   
mmExampleList :: [(Difficulty, Statement, Lemmas)]
mmExampleList = 
    [ easy $ [p, p :->: q, q :->: r] |- r
    , medium $ [p,  p :->: q] |-  r :->: q
--    , easy $ [p :->: (q :->: r) ] |- (p :->: q) :->: (p :->: r) opgave 4
  --  , medium $ [p :->: (q :->: r), (p :->: (q :->: r)) :->: ((p :->: q) :->: (p :->: r)) ] |- (p :->: q) :->: (p :->: r)
    , medium $ [  q :->: r]|-(p :->: q) :->: (p :->: r)
    , easy $ [p :->: q, p :->: (q :->: r)]|- p :->: r
    , medium $ [p :->: q, q :->: r]|- p :->: r
    , medium $ [ q, p :->: (q :->: r)]|- p :->: r
    , easy $ [] |- p :->: p
    , medium $ [p :->: r] |- p :->: (q :->: r)
    , medium $ [ p:->: (q :->: (r :->: s))] |- p :->: ((q :->: r) :->: (q :->: s))
    , medium $ [p :->: (q :->: r), q :->: (r :->: s)] |- p :->: (q :->: s)
    , medium $ [p :->: r, q :->: (r :->: s)] |- p :->: (q :->: s)
    , medium $ [p :->: (q :->: r)] |- q :->: (p :->: r)
    , medium $ [p :->: (q :->: r),  r :->: s] |-  p :->: (q :->: s)
    , medium $ [p :->: q, r :->: (q :->: s)]|- r :->: (p :->: s)
 --   , easy $ [] |-  p :->: ((p :->: q) :->: q)
    , medium $ [p :->: (q :->: r),  p:->: (q :->: (r :->: s))] |-  p :->: (q :->: s)
    , medium $ [p :->: r,  p:->: (q :->: (r :->: s))] |-  p :->: (q :->: s)
    , medium $ [p :->: (p :->: q)]|- p :->: q
    , medium $ [ p:->: (q :->: (p :->: r))] |- p :->: (q :->: r) 
    , medium $ []|- (p :->: (p :->: q)) :->: (p :->: q)
    , medium $ [p :->: (q :->: r)] |- p :->: ((s :->: q) :->: (s :->: r))
    , medium $ [] |- (p :->: q) :->: ((r :->: p) :->: (r :->: q))
    , medium $ [p :->: (Not q :->: Not r)] |- p :->: (r :->: q)
    , medium $ [p :->: Not q] |- p :->: (q :->: r)
    , medium $ [] |- (Not p :->: (p :->: q))     
    , medium $ [] |- (p :->: (Not p :->: q))
    , difficult $ [] |- ((Not p :->:  p) :->: p)
--   , difficult $ [p :->: (Not q :->: q)] |-  p :->: q
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")  
   s = Var (ShowString "s")

firstExamplesList :: [(Difficulty, Statement, Lemmas)]
firstExamplesList = 
   [easy $ [p, p :->: q] |- q 
   , easy $ [Not q :->: Not p] |- p :->: q
   , easy $ [] |- p :->: ((p :->: q) :->: q)
   , easy $ [p :->: (q :->: r) ] |- (p :->: q) :->: (p :->: r) 
   , (Easy, [] |- p :->: ( q :->: q), [lemma $ [p] |- q :->: q]) --23 
   , medium $ [p :->: q] |- (r :->: p) :->: (r :->: q)
   , medium $ [Not p]|- p :->: q
   , medium $ [(p :->: q) :->:r, q]|- r
   , (Medium, []|- p :->: ((p :->: q) :->: q), [lemma $ [] |- (p :->: q) :->: (p :->: q)])
   , (Medium, [ p :->: ( Not q :->: q)] |- p :->: q, [lemma $ [] |-  (Not q :->: q) :->: q])
   ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   
easy :: Statement -> (Difficulty, Statement, Lemmas)
easy st = (Easy, st, [])
   
medium :: Statement -> (Difficulty, Statement, Lemmas)
medium st = (Medium, st, [])

difficult :: Statement -> (Difficulty, Statement, Lemmas)
difficult st = (Difficult, st, [])