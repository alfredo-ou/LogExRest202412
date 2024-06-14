module Domain.Logic.Inductive.Strategies 
   ( inductiveStrategy, inductiveGuidedStrategy
   ) where

import Data.Maybe
import Domain.Logic.Inductive.Data
import Domain.Logic.Inductive.Definitions
import Domain.Logic.Inductive.RP
import Domain.Logic.Inductive.Relation
import Domain.Logic.Inductive.RelProof
import Domain.Logic.Inductive.Rules
import Domain.Logic.Inductive.ExprRules
import Domain.Math.Expr hiding ((.*.), (./.))
import Ideas.Common.Library

inductiveStrategy :: Strategy Inductive
inductiveStrategy = repeatS $ (liftSubProof inductiveStepStrategy ./. startNewSubProof)
                                    .*. repeatS (liftSubProof inductiveStepStrategy ./. startNewInductiveCase)

inductiveGuidedStrategy :: Strategy Inductive
inductiveGuidedStrategy = 
       try (check noOpen .*. showBaseCases) 
   .*. repeatS (liftSubProof inductiveStepStrategy ./. startNewBaseCase)
   .*. try showIH
   .*. try showInductiveCases
   .*. repeatS (liftSubProof inductiveStepStrategy ./. startNewInductiveCase)
 where
    noOpen x = all (isNothing . isOpen . snd) (proofs x)

-- voorlopige fix: alle expr regels proberen voor IH toepassing ivm setregel
inductiveStepStrategy :: Strategy (RelProof, Initial)
inductiveStepStrategy = 
   liftViewIn identity ((closeEqualProof .|. closeSameProof .|. closeLessProof) |> choice definitionCloseRules |> def |> (choice exprCloseRules |>  rs .|. valABStrategy))
                         .|. ( liftViewIn identity rs |> inductionHypothesisClose |> inductionHypothesis)      
 where
   def = onCurrentList definitionRules
   rs  = onCurrentList exprRules

   valABStrategy = 
      check (maybe False (\(_, rt, _) -> rt == LessThanOrEqual) . isOpen)
      .*. (stepAndClose (onCurrentBy LessThanOrEqual valAB) |> onCurrentBy LessThanOrEqual valAB)

onCurrentList :: [Rule Expr] -> Strategy RelProof
onCurrentList rs = choice (map (make extendUpper') rs) ./. choice (map (make extendLower') rs)
 where
   make f r = makeRule (getId r) $ \rp ->
      f Equal (showId r) (applyAll r) rp

maxSubProofs :: Int -- hack
maxSubProofs = 8  -- maximum $ map (length . language) (cases NL)

liftSubProof :: Strategy (RelProof, Initial) -> Strategy Inductive
liftSubProof s = 
   liftActiveProof s ./. 
   preference [ liftViewIn (inductivePair >>> inactiveProof n) s | n <- [ 0 .. maxSubProofs-1 ] ]
 where
   inductivePair = makeView (\a -> Just ((active a, proofs a), initial a)) (\((x1, x2), y) -> setActive x1 $ In x1 x2 y)
   
liftActiveProof :: Strategy (RelProof, Initial) -> Strategy Inductive
liftActiveProof = liftViewIn activeView
 where
   activeView :: View Inductive ((RelProof, Initial), (RelProof, Initial) -> Inductive)
   activeView = makeView f g
    where
      f a =
         case filter (isActive (active a)) (proofs a) of
            [(k, rp)] -> Just ((rp, initial a), \(rp2, st2) -> a { proofs = replace k rp2 (proofs a), initial = st2})
            _ -> Nothing
      g (new, back) = back new
      
      isActive (Just x) (Just y, _) = x == y
      isActive _ _ = False

      replace _ _ [] = []
      replace k v (x:xs)
         | k == fst x = (k, v) : xs
         | otherwise  = x : replace k v xs

inactiveProof :: Eq k => Int -> View ((Maybe k, [(Maybe k, a)]), t) ((a, t), a -> (Maybe k, [(Maybe k, a)]))
inactiveProof n = makeView f g
 where
   f ((act, xs), t) = 
      case splitAt n xs of
         (_, [])         -> Nothing
         (as, (k, b):bs) 
            | isJust k && k == act -> Nothing
            | otherwise            -> Just ((b, t), \c -> (k, as ++ (k, c):bs))
   g ((c, t), back) = (back c, t)