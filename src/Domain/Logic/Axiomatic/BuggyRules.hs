module Domain.Logic.Axiomatic.BuggyRules (buggyRules) where

import Data.Maybe
import Ideas.Common.Library hiding (label)
import Domain.Logic.Axiomatic.Label
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.LinearProof
import Domain.Logic.Axiomatic.Rules
import Domain.Logic.Formula
import qualified Data.Set as S
import Control.Monad

-- order in the list determines in which order the buggy rules are tried
buggyRules :: [Rule AxiomaticProof]
buggyRules = [bugMPfw0, bugMPfw9, bugMPfw2,bugMPfw3,bugMPfw4,bugMPfw5, bugMPfw6, bugMPfw7,bugMPfw8,
              bugMPm1, bugMPm2,  bugMPm41, bugMPm42,
              bugMPcl1,bugMPcl2, 
              bugMPDefault,bugMPDefault2, 
              bugDedbw1,bugDedcl0, bugDedcl4,bugDedcl1, bugDed1, bugDedcl2, bugDedcl3, bugDedFw 
             , bugGoal1R, bugGoal2R
             ]

checkInput1 :: Ref a -> (a -> t -> Bool) -> Trans t t
checkInput1 r1 f = transInput1 r1 $ \x p -> if f x p then Just p else Nothing

checkInput2 :: Ref a -> Ref b -> (a -> b -> t -> Bool) -> Trans t t
checkInput2 r1 r2 f = transInput2 r1 r2 $ \x y p -> if f x y p then Just p else Nothing

checkInput3 :: Ref a -> Ref b -> Ref c -> (a -> b -> c -> t -> Bool) -> Trans t t
checkInput3 r1 r2 r3 f = transInput3 r1 r2 r3 $ \x y z p -> if f x y z p then Just p else Nothing

transCheck :: (a -> Bool) -> Transformation a
transCheck p = makeTrans $ \x -> [x | p x]

checkInOut :: Trans a i -> Trans o x -> Trans (i, a) o -> Transformation a
checkInOut inT outT = outputOnlyWith outT . inputWith inT

readRef3M :: Ref a -> Ref b -> Ref c -> Trans x (a, b, Maybe c)
readRef3M r1 r2 r3 = readRef2 r1 r2 &&& readRefMaybe r3 >>> arr f
  where 
   f ((a, b), c) = (a, b, c)
   
readRef3M1 :: Ref a -> Ref b -> Ref c -> Trans x (Maybe a, b, c)
readRef3M1 r1 r2 r3 = (readRefMaybe r1 &&& readRef r2) &&& readRef r3 >>> arr f
  where
   f ((a, b), c) = (a, b, c)
   
readRef3M2 :: Ref a -> Ref b -> Ref c -> Trans x (a, Maybe b, c)
readRef3M2 r1 r2 r3 = (readRef r1 &&& readRefMaybe r2) &&& readRef r3 >>> arr f
  where
   f ((a, b), c) = (a, b, c)   
   
readRef3MM :: Ref a -> Ref b -> Ref c -> Trans x (Maybe a, b, Maybe c)
readRef3MM r1 r2 r3 = (readRefMaybe r1 &&& readRef r2) &&& readRefMaybe r3 >>> arr f
  where
   f ((a, b), c) = (a, b, c)      


-- Buggy rules

-- schema verkeerd ingevuld
mpForwardBug0 :: Trans ((Int, Int, Maybe Int), AxiomaticProof) SLogic
mpForwardBug0 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (verkeerdom cs1 cs2)
   return cs2
 where
   verkeerdom (p :->:q) r = p == r 
   verkeerdom _ _ = False  

bugMPfw0 :: Rule AxiomaticProof
bugMPfw0 = describe "buggy mp" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw0") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef psiRef) mpForwardBug0   

bugMPfw2 :: Rule AxiomaticProof
bugMPfw2 = describe "buggy mp" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw2") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug22         

mpForwardBug2 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug2 n1 n2 prf = fromMaybe False $ do
   guard (isMotivated n1 prf)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (inImpl cs1 cs2)
 where
   inImpl q (p :->: (r :->: s)) = p /= q && q == r
   inImpl _ _ = False   
   
mpForwardBug22 :: Trans ((Int, Int, Maybe Int), AxiomaticProof) (SLogic, SLogic)
mpForwardBug22 = makeTrans $ \((n1, n2, mn3), prf) -> do
   guard (isNothing mn3)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (inImpl cs1 cs2)
   return (f cs1 cs2)
 where
   inImpl q (p :->: (r :->: s)) = p /= q && q == r
   inImpl _ _ = False   
   f q (p :->: (r :->: s)) = (q, p)
   
bugMPfw3 :: Rule AxiomaticProof
bugMPfw3 = describe "buggy mp" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw3") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug32       

mpForwardBug3 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug3 n1 n2 prf = fromMaybe False $ do
   guard (isMotivated n1 prf)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (transImpl cs1 cs2)
 where
   transImpl (p :->:q) (r :->: s) = q == r
   transImpl _ _ = False      
   
mpForwardBug32 ::  Trans ((Int, Int, Maybe Int), AxiomaticProof) (SLogic, SLogic)
mpForwardBug32 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- getTerm n1 prf
--   guard (isNothing mn3) (omdat de nummering consistent is, is er geen aparte close variant nodig?!
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (transImpl cs1 cs2)
   return (f cs1 cs2)
 where
   transImpl (p :->:q) (r :->: s) = q == r
   transImpl _ _ = False      

   f p (q :->:r) = (p, q)

bugMPfw4 :: Rule AxiomaticProof
bugMPfw4 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw4") $
   checkInput2 n1Ref n2Ref mpForwardBug4

mpForwardBug4 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug4 n1 n2 prf = fromMaybe False $ do
   st1 <- getTerm n1 prf
 --  guard (not(null (label pl))) overbodig?
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (haakjesImpl cs1 cs2)
 where
   haakjesImpl (p :->:q) (r :->:(s :->: t)) = p == r && q == s
   haakjesImpl _ _ = False
   

bugMPfw5 :: Rule AxiomaticProof
bugMPfw5 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw5") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug52   

mpForwardBug5 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug5 n1 n2 prf = fromMaybe False $ do
   guard (isMotivated n1 prf)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (equImpl cs1 cs2)
 where
   equImpl r (p :->:q)  = p /= r && eqLogic p r
   equImpl _ _ = False    
   
mpForwardBug52 :: Trans ((Int, Int, Maybe Int), AxiomaticProof) (SLogic, SLogic)
mpForwardBug52 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- getTerm n1 prf
--   guard (isNothing mn3) overbodig
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (equImpl cs1 cs2)
   return (xs cs1 cs2)
 where
   equImpl r (p :->:q)  = p /= r && eqLogic p r
   equImpl _ _ = False
   xs r (p :->:q) = (r, p)

bugMPfw6 :: Rule AxiomaticProof
bugMPfw6 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw6") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug62         

mpForwardBug6 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug6 n1 n2 prf = fromMaybe False $ do
   guard (isMotivated n1 prf)
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (right cs1 cs2)
 where
   right r (p :->:q)  = p /= r && (r == q)
   right _ _ = False    
   
mpForwardBug62 :: Trans ((Int, Int, Maybe Int), AxiomaticProof) (SLogic, SLogic)
mpForwardBug62 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- getTerm n1 prf
 --  guard (isNothing mn3)
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (right cs1 cs2)
   return (xs cs1 cs2) 
 where
   right r (p :->:q)  = p /= r && (r == q)
   right _ _ = False      
   xs r (p :->:q) = (r, p)
     
bugMPfw7 :: Rule AxiomaticProof
bugMPfw7 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw7") $ 
   checkInput2 n1Ref n2Ref mpForwardBug7

mpForwardBug7 :: Int -> Int -> AxiomaticProof -> Bool
mpForwardBug7 n1 n2 prf = fromMaybe False $ do
   st1 <- getTerm n1 prf
--   guard (not(null (label pl)))
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (haakjes cs1 cs2)
 where
   haakjes r ((p :->:q):->: s)  = p == r 
   haakjes _ _ = False    

bugMPfw8 :: Rule AxiomaticProof
bugMPfw8 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw8") $
   checkInOut (readRef3MM n1Ref n2Ref n3Ref) (writeRef psiRef) mpForwardBug82      

mpForwardBug82 :: Trans ((Maybe Int, Int, Maybe Int), AxiomaticProof) SLogic
mpForwardBug82 = makeTrans $ \((mn1, n2, mn3), prf) -> do
   st2 <- getTerm n2 prf
   let cs2 = consequent st2
   guard (noImpl cs2)
   return cs2
 where
   noImpl (p :->:q)  = False 
   noImpl _         = True  
   
bugMPfw9 :: Rule AxiomaticProof
bugMPfw9 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw9") $
      checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef phiRef) mpForwardBug9      

mpForwardBug9 :: Trans ((Int, Int, Maybe Int), AxiomaticProof) SLogic
mpForwardBug9  = makeTrans $ \((n1, n2, mn3), prf) -> do
 --  guard (isNothing mn3) 
   guard (isNotMotivated n1 prf || isNotMotivated n2 prf)
   st1 <- getTerm n1 prf
   return (consequent st1)  --eigenlijk is hier geen return nodig, maar zonder krijg ik het niet aan de praat
   
bugMPm1 :: Rule AxiomaticProof
bugMPm1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m1") $
   checkInOut (readRef3M1 n1Ref n2Ref n3Ref) (writeRef asRef) mpMid12     

mpMid12 :: Trans ((Maybe Int, Int, Int), AxiomaticProof) [SLogic]
mpMid12 = makeTrans $ \((mn1, n2, n3), prf) -> do
   guard (isNotMotivated n3 prf && isNothing mn1)
   st1 <- getTerm n2 prf
   st2 <- getTerm n3 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       cs1 = consequent st1
       cs2 = consequent st2
   guard (fits cs1 cs2 && not (as1 `S.isSubsetOf` as2))
   return $ S.toList (S.difference as1 as2)
 where
   fits (p :->: q) r = q == r 
   fits _ _ = False     
   
bugMPm2 :: Rule AxiomaticProof
bugMPm2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m2") $
   checkInOut (readRef3M2 n1Ref n2Ref n3Ref) (writeRef asRef) mpMid22    

  
mpMid22 :: Trans ((Int, Maybe Int, Int), AxiomaticProof) [SLogic]
mpMid22 = makeTrans $ \((n1, mn2, n3), prf) -> do
   guard (isNotMotivated n3 prf && isNothing mn2)
   st1 <- getTerm n1 prf
   st2 <- getTerm n3 prf
   let as1 = assumptions st1
       as2 = assumptions st2
   guard  (not (as1 `S.isSubsetOf` as2))  
   return $ S.toList (S.difference as1 as2)

bugMPm42 :: Rule AxiomaticProof
bugMPm42 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m42") $
   checkInOut (readRef3M1 n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpMid42  

mpMid42 :: Trans ((Maybe Int, Int, Int), AxiomaticProof) (SLogic, SLogic)
mpMid42 = makeTrans $ \((n1, n2, n3), prf) -> do
   guard (isNotMotivated n3 prf)  
   st1 <- getTerm n2 prf
   st2 <- getTerm n3 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (nofits cs1 cs2)
   return (f cs1 cs2)
 where
   nofits (p :->: q) r = q /= r 
   nofits _ _ = False     
   f (p :->: q) r = (q, r)

bugMPm41 :: Rule AxiomaticProof
bugMPm41 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m4") $
   checkInOut (readRef3M1 n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpMid41  

mpMid41 :: Trans ((Maybe Int, Int, Int), AxiomaticProof) (SLogic, SLogic)
mpMid41 = makeTrans $ \((mn1, n2, n3), prf) -> do
   guard (isNotMotivated n3 prf && isNothing mn1)
   st1 <- getTerm n2 prf
   st2 <- getTerm n3 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (nofits cs1 cs2)
   return (f cs1 cs2)
 where
   nofits (p :->: q) r = q /= r 
   nofits _ _ = False     
   f (p :->: q) r = (q, r)

    
bugMPcl1 :: Rule AxiomaticProof
bugMPcl1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl1") $
   checkInOut (readRef3 n1Ref n2Ref n3Ref) (writeRef asRef) mpCloseBug12   

-- in een applicatie van MP (phi, phi -> psi, psi) is psi = n3 en phi = n1
mpCloseBug1 :: Int -> Int -> Int -> AxiomaticProof -> Bool
mpCloseBug1 n1 n2 n3 prf =  fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   st3 <- getTerm n3 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       as3 = assumptions st3
   return (nosubs as1 as2 as3 && fits (consequent st3) (consequent st1) (consequent st2))
  where
   nosubs as1 as2 as3 = not (S.union as1 as2  `S.isSubsetOf` as3) 
   fits q (p :->: r) (s :->: t) =  (q == r && p == (s :->: t)) ||(q == t && s == (p :->: q))
   fits q (p :->: r) s  = q == r && p == s
   fits q s (p :->: r) = q == r && p == s
   fits _ _ _ = False

   
mpCloseBug12 :: Trans ((Int, Int, Int), AxiomaticProof) [SLogic]
mpCloseBug12 = makeTrans $ \((n1, n2, n3), prf) -> do   
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   st3 <- getTerm n3 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       as3 = assumptions st3
   guard (nosubs as1 as2 as3 && fits (consequent st3) (consequent st1) (consequent st2))
   return  $ S.toList as3
  where
   nosubs as1 as2 as3 = not (S.union as1 as2  `S.isSubsetOf` as3) 
   fits q (p :->: r) (s :->: t) =  (q == r && p == (s :->: t)) ||(q == t && s == (p :->: q))
   fits q (p :->: r) s  = q == r && p == s
   fits q s (p :->: r) = q == r && p == s
   fits _ _ _ = False   
   

 
bugMPcl2 :: Rule AxiomaticProof
bugMPcl2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl2") $
   checkInOut (readRef3 n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpCloseBug22   

mpCloseBug2 :: Int -> Int -> Int -> AxiomaticProof-> Bool
mpCloseBug2 n1 n2 n3 prf = fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   st3 <- getTerm n3 prf
   let cs1 = consequent st1
       cs2 = consequent st2
       cs3 = consequent st3
   return (inImpl cs1 cs2 cs3)
 where
   inImpl q (p  :->: (r :->: s)) (x :->: y) = q == r && p == x && s == y
   inImpl _ _ _= False  
  
mpCloseBug22 :: Trans ((Int, Int, Int), AxiomaticProof) (SLogic, SLogic)
mpCloseBug22 = makeTrans $ \((n1, n2, n3), prf) -> do 
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   st3 <- getTerm n3 prf
   let cs1 = consequent st1
       cs2 = consequent st2
       cs3 = consequent st3
   guard (inImpl cs1 cs2 cs3)
   return (f cs1 cs2)
 where
   inImpl q (p :->: (r :->: s)) (x :->: y) = q == r && p == x && s == y
   inImpl _ _ _= False

   f q (p :->: _) = (q, p)

bugMPDefault :: Rule AxiomaticProof
bugMPDefault = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-default") $
   checkInput3 n1Ref n2Ref n3Ref $ \x y z -> mpDefaultBug z y x
   
mpDefaultBug :: Int -> Int -> Int -> AxiomaticProof -> Bool
mpDefaultBug n1 n2 n3 prf = True

bugMPDefault2 :: Rule AxiomaticProof
bugMPDefault2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-default2") $
   checkInput2 n1Ref n2Ref mpDefaultBug2
   
mpDefaultBug2 ::  Int -> Int -> AxiomaticProof -> Bool
mpDefaultBug2 n1 n2  prf = True

--  deduction rules   -------------------------------------------------------------------------


bugDed1 :: Rule AxiomaticProof
bugDed1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-1") $
   checkInOut (readRef nRef) (writeRef phiRef) dedBug2

dedBug2 :: Trans (Int, AxiomaticProof) SLogic
dedBug2 = makeTrans $ \(n, prf) -> do
   st <- getTerm n prf
   let cs = consequent st
   guard (noImpl cs) 
   return cs
  where
   noImpl (p :->: q) = False 
   noImpl _          = True

bugDedbw1 :: Rule AxiomaticProof
bugDedbw1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggybw-1") $
   checkInput1 nRef isMotivated   

bugDedcl0 :: Rule AxiomaticProof
bugDedcl0 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggycl-0") $
   checkInput2 n1Ref n2Ref dedBugcl0   
   
dedBugcl0 :: Int -> Int -> AxiomaticProof  -> Bool
dedBugcl0  n1 n2  prf =  fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf 
   let cs1 = consequent st1
       cs2 = consequent st2
   return (isMotivated n2 prf && nofit cs1 cs2) 
  where
   nofit p (q :->:r) = p /= q
   nofit _ _         = True

bugDedFw :: Rule AxiomaticProof
bugDedFw = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggyfw") $
   checkInput1 nRef dedBugFw   

dedBugFw ::  Int -> AxiomaticProof  -> Bool
dedBugFw  n   prf =  fromMaybe False $ do
   st <- getTerm n prf
   let cs = consequent st
   return (not (isMotivated n prf) && impl cs) 
  where
   impl (q :->:r)  = True
   impl _         = False
   
dedBug:: Int -> AxiomaticProof -> Maybe Environment
dedBug n  prf = do
   st <- getTerm n prf
   let cs = consequent st
   guard (noImpl cs) 
   return (singleBinding phiRef cs)
  where
   noImpl (p :->: q) = False 
   noImpl _          = True
 
dedBugcl1::Int -> Int -> AxiomaticProof  -> Bool
dedBugcl1 n1 n2  prf =  fromMaybe False $ do
   st <- getTerm n2 prf
   let cs = consequent st
   return (noImpl cs) 
  where
   noImpl (p :->: q) = False 
   noImpl _          = True
   
bugDedcl1 :: Rule AxiomaticProof
bugDedcl1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-2") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef phiRef) dedBugcl12      
   
dedBugcl12::Trans ((Int, Int), AxiomaticProof) SLogic
dedBugcl12 = makeTrans $ \((n1, n2), prf) -> do
    st <- getTerm n2 prf
    let cs = consequent st
    guard (noImpl cs) 
    return cs
  where
    noImpl (p :->: q) = False 
    noImpl _          = True
  
dedBugcl2::Int -> Int -> AxiomaticProof  -> Bool
dedBugcl2 n1 n2  prf =  fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   return (noFit cs1 cs2) 
  where
   noFit r (p :->: q) = r /= q 
   noFit _ _          = False  

bugDedcl2 :: Rule AxiomaticProof
bugDedcl2 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-3") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef2 phiRef psiRef) dedBugcl22   
   
dedBugcl22::Trans ((Int, Int), AxiomaticProof) (SLogic, SLogic)
dedBugcl22 = makeTrans $ \((n1, n2), prf) -> do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (noFit cs1 cs2) 
   return (f cs1 cs2)
  where
   noFit  r (p :->: q) = r /= q 
   noFit  _ _          = False  

   f r (p :->: q) = (r, q)
     
bugDedcl3 :: Rule AxiomaticProof
bugDedcl3 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-4") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef2 asRef phiRef) dedBugcl32         
   
dedBugcl3::Int -> Int -> AxiomaticProof  -> Bool
dedBugcl3 n1 n2  prf =  fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       cs2 = consequent st2
   return (noFit as1 as2 cs2) 
  where
   noFit  as1 as2 (p:->: q) = not (as1 `S.isSubsetOf` S.delete p as2)
   noFit  _ _ _         = False    
  
dedBugcl32::Trans ((Int, Int), AxiomaticProof) ([SLogic], SLogic)
dedBugcl32 = makeTrans $ \((n1, n2), prf) -> do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       cs2 = consequent st2
   guard  (noFit as1 as2 cs2)   
   return (f as1 cs2) 
  where
   noFit as1 as2 (p :->: _) = not (S.delete p as1 `S.isSubsetOf` as2) 
   noFit _ _ _              = False   

   f as1 (p:->: q) = (S.toList as1, p)
   
bugDedcl4 :: Rule AxiomaticProof
bugDedcl4 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-5") $ 
   checkInput2 n1Ref n2Ref dedBugcl4
   
dedBugcl4::Int -> Int -> AxiomaticProof  -> Bool
dedBugcl4 n1 n2  prf =  fromMaybe False $ do
   st1 <- getTerm n1 prf
   st2 <- getTerm n2 prf
   let as1 = assumptions st1
       as2 = assumptions st2
       cs1 = consequent st1
       cs2 = consequent st2
   return (mp as1 as2 cs1 cs2) 
  where
   mp  as1 as2 (p:->: q) r =  ((p `S.insert` as1) `S.isSubsetOf` as2) && q == r  
   mp  _ _ _ _        = False   
   
--------------------------------------
-- goal rules

bugGoal1R :: Rule AxiomaticProof
bugGoal1R = describe "buggy goal" $ buggy $ siblingOf goalId $ ruleTrans (goalId # "buggy-gl1") $
   checkInput1 stRef (const . not . validStatement)
   
bugGoal2R :: Rule AxiomaticProof
bugGoal2R = describe "buggy goal" $ buggy $ siblingOf goalId $ ruleTrans (goalId # "buggy-gl2") $
   checkInput1 stRef bugGoal2
     
bugGoal2 ::Statement -> AxiomaticProof -> Bool
bugGoal2 st prf = validStatement st && (st `subStatement` exgoal || exgoal `subStatement` st)
  where 
    exgoal = fromJust (getTerm 1000 prf)