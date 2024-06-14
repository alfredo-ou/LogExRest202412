{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-----------------------------------------------------------------------------

module Domain.Logic.Parser
   ( parseLogic, parseLogicPars, parseLogicUnicodePars, parseLogicProof
   , parseLogicProofs, parseConsequence, parseStatement, parserSLogic
   , associateToRight
   ) where

import Domain.Logic.Formula
import Ideas.Common.Environment
import Ideas.Utils.Prelude (ShowString(..))
import Ideas.Utils.Uniplate
import Ideas.Utils.Parsing
import qualified Text.ParserCombinators.Parsec.Token as P

-----------------------------------------------------------
--- Parser

parseLogic :: String -> Either String SLogic
parseLogic = parseBalanced (parserSLogic False False)

parseLogicUnicode :: String -> Either String SLogic
parseLogicUnicode = parseBalanced (parserSLogic True False)

parseLogicPars :: String -> Either String SLogic
parseLogicPars input =
     either (Left . ambiguousOperators parseLogic input) suspiciousVariable
   $ parseBalanced (parserSLogic False True) input

parseLogicUnicodePars :: String -> Either String SLogic
parseLogicUnicodePars input =
   either (Left . ambiguousOperators parseLogicUnicode input) suspiciousVariable
   $ parseBalanced (parserSLogic True True) input

parseBalanced :: Parser a -> String -> Either String a
parseBalanced p input =
   maybe (parseSimple p input) (Left . show) (balanced [('(', ')')] input)

parseLogicProof :: Bool -> String -> Either String (SLogic, SLogic)
parseLogicProof unicode input =
   case balanced [('(',')')] input of
      Just msg -> Left (show msg)
      Nothing  -> case splitIs input of
         Just (lhs, _) ->
            case balanced [('(',')')] lhs of
               Just e2 -> Left (show e2)
               Nothing -> parseLogicProof2 unicode input
         Nothing -> Left "Expecting =="

splitIs :: String -> Maybe (String, String)
splitIs = rec []
 where
   rec acc ('=':'=':xs) = Just (reverse acc, xs)
   rec acc (x:xs)       = rec (x:acc) xs
   rec _   []           = Nothing

parseLogicProof2 :: Bool -> String -> Either String (SLogic, SLogic)
parseLogicProof2 unicode = parseSimple $ do
   p <- parserSLogic unicode True
   reservedOp "=="
   q <- parserSLogic unicode True
   return (p, q)

parseLogicProofs :: String -> Either String [(SLogic, SLogic)]
parseLogicProofs = parseSimple $ commaSep1 $ do
   let unicode = False
   p <- parserSLogic unicode True
   reservedOp "=="
   q <- parserSLogic unicode True
   return (p, q)

parseConsequence :: Bool -> String -> Either String ([SLogic], SLogic)
parseConsequence unicode = parseSimple $ do
   ps <- commaSep1 (parserSLogic unicode True)
   reservedOp "=>"
   q <- parserSLogic unicode True
   return (ps, q)

parseStatement :: Bool -> String -> Either String ([SLogic], SLogic)
parseStatement unicode = parseSimple $ do
   ps <- commaSep (parserSLogic unicode True)
   reservedOp "|-"
   q <- parserSLogic unicode True
   return (ps, q)

-- generalized parser
parserSLogic :: Bool -> Bool -> Parser SLogic
parserSLogic unicode extraPars = pLogic
 where
   pLogic
      | extraPars = atom <**> option id composed
      | otherwise = buildExpressionParser table atom

   composed = choice
      [ flip (:->:)  <$ reservedOp implSym  <*> atom
      , flip (:<->:) <$ reservedOp equivSym <*> atom
      , (\xs x -> ors (x:xs))  <$> many1 (reservedOp disjSym >> atom)
      , (\xs x -> ands (x:xs)) <$> many1 (reservedOp conjSym >> atom)
      ]

   atom = choice
      [ T <$ P.reserved lexer trSym
      , F <$ P.reserved lexer flSym
      , Var . ShowString <$> P.identifier lexer
      , P.parens lexer pLogic
      , Not <$ reservedOp negSym <*> atom
      ]

   table =
      [ [Infix ((:->:)  <$ reservedOp implSym)  AssocRight ]
      , [Infix ((:&&:)  <$ reservedOp conjSym)  AssocRight ]
      , [Infix ((:||:)  <$ reservedOp disjSym)  AssocRight ]
      , [Infix ((:<->:) <$ reservedOp equivSym) AssocRight ]
      ]

   (implSym, equivSym, conjSym, disjSym, negSym, trSym, flSym)
      | unicode   = unicodeTuple
      | otherwise = asciiTuple

lexer :: P.TokenParser a
lexer = P.makeTokenParser $ emptyDef
   { reservedNames   = ["T", "F"]
   , reservedOpNames = ["~", "<->", "->", "||", "/\\", "==", "=>"]
   , identStart      = lower
   , identLetter     = lower
   , opStart         = fail ""
   , opLetter        = fail ""
   }

reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer

commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lexer

commaSep1 :: Parser a -> Parser [a]
commaSep1 = P.commaSep1 lexer

-----------------------------------------------------------
--- Helper-functions for syntax warnings

ambiguousOperators :: (String -> Either a b) -> String -> String -> String
ambiguousOperators p s err =
   let msg = "Syntax error: ambiguous use of operators (write parentheses)"
   in either (const err) (const msg) (p s)

-- Report variables
suspiciousVariable :: SLogic -> Either String SLogic
suspiciousVariable r =
   case filter p (map fromShowString (varsLogic r)) of
      v:_ -> Left $ "Unexpected variable " ++ v
                 ++ ". Did you forget an operator?"
      _   -> Right r
 where
   p xs = length xs > 1 && all (`elem` "pqrst") xs

-----------------------------------------------------------
--- Pretty-Printer

associateToRight :: Logic a -> Logic a
associateToRight p@(_ :&&: _) = ands (map associateToRight (conjunctions p))
associateToRight p@(_ :||: _) = ors (map associateToRight (disjunctions p))
associateToRight p = descend associateToRight p

instance Read SLogic where
   readsPrec _ s =
      case parseLogicPars s of
         Left _  -> []
         Right p -> [(p, "")]

instance Reference SLogic
