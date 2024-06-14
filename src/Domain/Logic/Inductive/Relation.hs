module Domain.Logic.Inductive.Relation 
   ( Relation, makeRelation
   , leftHandSide, rightHandSide, relationType
     -- relation type
   , RelType(..), isNumerical, combineRelType, combineRelTypes, compareRelType, weakenRelType
   , reflexive, swapRelType
   , relTypeDecoder
   , relationSymbols
   ) where

import Ideas.Common.Rewriting
import Ideas.Text.OpenMath.Dictionary.Relation1
import Ideas.Text.JSON
import Ideas.Utils.Prelude (readM)

data Relation t a = R
   { relationType  :: t
   , leftHandSide  :: a
   , rightHandSide :: a
   }
 deriving Eq

instance (Show t, Show a) => Show (Relation t a) where
   show r = unwords [show (leftHandSide r), show (relationType r), show (rightHandSide r)]

instance Functor (Relation t) where
   fmap f (R t x y) = R t (f x) (f y)

instance (IsTerm t, IsTerm a) => IsTerm (Relation t a) where
   toTerm (R t x y) = TList [toTerm t, toTerm x, toTerm y]
   termDecoder = tList3 R termDecoder termDecoder termDecoder

makeRelation :: t -> a -> a -> Relation t a
makeRelation = R

---------------------------------------------------------------------------------------

data RelType = GreaterThan| GreaterThanOrEqual |  LessThan | LessThanOrEqual | Equal -- numerical relations
             | Equivalence -- logical relation
 deriving (Eq, Ord, Enum)
 
instance Show RelType where
   show = showRelType
 
instance Read RelType where
   readsPrec _ = maybe [] (\x -> [(x, "")]) . readRelType 
 
instance IsTerm RelType where
   toTerm rt = maybe (error $ "unknown relationtype" ++ show rt) symbol (lookup rt relationSymbols)
   termDecoder =
      foldr (<|>) empty
         [ rt <$ tCon0 s
         | (rt, s) <- relationSymbols
         ]

swapRelType :: RelType -> RelType
swapRelType GreaterThan        = LessThan
swapRelType GreaterThanOrEqual = LessThanOrEqual
swapRelType LessThan           = GreaterThan
swapRelType LessThanOrEqual    = GreaterThanOrEqual
swapRelType Equal              = Equal
swapRelType Equivalence        = Equivalence

isNumerical :: RelType -> Bool
isNumerical = (`elem` [LessThan, LessThanOrEqual, Equal])

isNumericalDecreasing :: RelType -> Bool
isNumericalDecreasing = (`elem` [GreaterThan, GreaterThanOrEqual, Equal])

combineRelTypes :: [RelType] -> Maybe RelType
combineRelTypes [] = Nothing
combineRelTypes xs = foldl1 op (map Just xs)
 where
   op :: Maybe RelType -> Maybe RelType -> Maybe RelType
   op (Just x) (Just y) = combineRelType x y 
   op _ _ = Nothing
 
combineRelType :: RelType -> RelType -> Maybe RelType
combineRelType x y
   | isNumericalDecreasing  x == isNumericalDecreasing y = Just (x `min` y)
   | isNumerical x == isNumerical y = Just (x `min` y)
   | otherwise = Nothing

-- expected reltype, provided reltyp
compareRelType :: RelType -> RelType -> Bool
compareRelType LessThanOrEqual rt = isNumerical rt
compareRelType GreaterThanOrEqual rt = isNumericalDecreasing rt
compareRelType rt1 rt2            = rt1 == rt2

weakenRelType :: [(RelType, RelType)]  
weakenRelType =
   [ (Equal, LessThanOrEqual), (Equal, GreaterThanOrEqual) 
   , (LessThan, LessThanOrEqual), (GreaterThan, GreaterThanOrEqual)
   ]
   ++
   [ (t, t) | t <- [GreaterThan .. Equivalence] ]

reflexive :: RelType -> Bool
reflexive tp = tp `elem` [Equal, LessThanOrEqual, GreaterThanOrEqual, Equivalence]

showRelType :: RelType -> String
showRelType Equal              = "="
showRelType LessThan           = "<"
showRelType LessThanOrEqual    = "<="
showRelType GreaterThan        = ">"
showRelType GreaterThanOrEqual = ">="
showRelType Equivalence        = "<=>"

readRelType :: String -> Maybe RelType
readRelType "="   = Just Equal
readRelType "<"   = Just LessThan
readRelType ">="  = Just GreaterThanOrEqual
readRelType ">"   = Just GreaterThan
readRelType "<="  = Just LessThanOrEqual
readRelType "<=>" = Just Equivalence
readRelType _     = Nothing

relationSymbols :: [(RelType, Symbol)]
relationSymbols =
   [ (Equal,           newSymbol eqSymbol)
   , (LessThan,        newSymbol ltSymbol)
   , (LessThanOrEqual, newSymbol leqSymbol)
   , (GreaterThan,        newSymbol gtSymbol)
   , (GreaterThanOrEqual, newSymbol geqSymbol)
   , (Equivalence,     newSymbol "equivalence")
   ]

relTypeDecoder :: DecoderJSON RelType
relTypeDecoder = jKey "type" $ jString >>= \s -> 
   case readM s of
      Just rt -> return rt
      Nothing -> errorStr "invalid reltype"