module Domain.Logic.Axiomatic.Motivation
   ( Motivation, motivation, motivationId
   ) where

import Data.Char
import Data.List (intercalate)
import Ideas.Common.Rewriting
import Ideas.Common.Id
import Ideas.Text.JSON
import Ideas.Text.Latex

data Motivation a = M Id [a]
 deriving (Eq, Ord)

instance Show a => Show (Motivation a) where
   show (M l as) = "[" ++ intercalate ", " (unqualified l : map show as) ++ "]"

instance Read a => Read (Motivation a) where
   readsPrec _ s = 
      case dropWhile isSpace s of
         '[':s1 -> let (s2, s3) = break (`elem` ",]") s1
                       (s4, s5) = break (== ']') s3
                       is = read ('[' : dropWhile (==',') s4 ++ "]")
                   in [(motivation s2 is, drop 1 s5)]
         _ -> []

instance Functor Motivation where
   fmap f (M l as) = M l (fmap f as)

instance Foldable Motivation where
   foldMap f (M _ as) = mconcat (map f as)

instance Traversable Motivation where
   traverse f (M l as) = M l <$> traverse f as

instance IsId (Motivation a) where
   newId = motivationId

instance HasId (Motivation a) where
   getId = motivationId
   changeId f (M l as) = M (f l) as

instance IsTerm a => IsTerm (Motivation a) where
   toTerm (M l as) = toTerm (l, as)
   termDecoder = uncurry M <$> termDecoder

instance InJSON a => InJSON (Motivation a) where
   jsonBuilder (M l as) =
      "label" .= show l <> if null as then mempty else "references" .= as
   jsonDecoder = motivation 
      <$> jKey "label" jString
      <*> (jKey "references" jsonDecoder <|> pure [])

instance ToLatex a => ToLatex (Motivation a) where
   toLatex (M l as) = commas (toLatex (show l) : map toLatex as)

motivation :: IsId n => n -> [a] -> Motivation a
motivation = M . newId

motivationId :: Motivation a -> Id
motivationId (M l _) = l