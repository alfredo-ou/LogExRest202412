module Domain.Logic.Inductive.Parser (parseInductiveExpr, exprDecoder) where

import Ideas.Utils.Parsing
import Ideas.Utils.Uniplate
import Ideas.Text.JSON hiding ((<|>), many)
import Domain.Math.Expr hiding (pExpr)
import Domain.Algebra.Boolean
import Domain.Logic.Inductive.Symbols
import qualified Text.ParserCombinators.Parsec.Token as P
import Prelude hiding ((^))

instance InJSON Expr where
   toJSON = String . showExpr

   fromJSON (String s) = parseInductiveExpr s
   fromJSON _          = fail "expecting string for expr"

-- pretty-printing with associativity for + and *
showExpr :: Expr -> String
showExpr = show . f 
 where
   f (x :+: (y :+: z)) = f ((x :+: y) :+: z)
   f (x :*: (y :*: z)) = f ((x :*: y) :*: z)
   f expr = descend f expr

exprDecoder :: DecoderJSON Expr
exprDecoder = jString >>= parseInductiveExpr

parseInductiveExpr :: Monad m => String -> m Expr
parseInductiveExpr s =
   case parseSimple pExpr s of
      Left msg -> error $ s ++ "\n" ++ msg
      Right a  -> return a

pExpr :: Parser Expr
pExpr = buildExpressionParser exprTable exprNeg

-- function application (in term) binds stronger than unary negation
exprNeg :: Parser Expr
exprNeg = (complement <$ reservedOp "~" <*> exprNeg) <|> term

term :: Parser Expr
term =
   choice [ f <$ reserved s | (s, f) <- funs ] <*> many atom
 <|>
   choice [ f <$ reserved s | (s, f) <- funs1 ] <*> atom
 <|> 
   choice [ f <$ reserved s | (s, f) <- funs2 ] <*> atom <*> atom
 <|>
   choice [ f <$ reserved s | (s, f) <- funs3 ] <*> atom <*> atom <*> atom
 <|> atom

atom :: Parser Expr
atom = choice
   [ do notFollowedBy (char '-')
        either fromInteger fromDouble <$> naturalOrFloat
   -- , variable <$> identifier
   -- , pi <$ reserved "pi"
   , choice [ Var s <$ reserved s | s <- vars ]
   , choice [ e <$ reserved s | (s, e) <- cons ]
   , parens pExpr
   ]

--------------------------------------------------------------------------

-- to do: import lists from Data dan break cyclic dependency
vars :: [String] 
vars = ["phi", "psi", "chi", "p", "q", "r"]

cons :: [(String, Expr)]
cons = [("T", true), ("F", false)]

funs :: [(String, [Expr] -> Expr)]
funs = [("set", set)]

funs1 :: [(String, Expr -> Expr)]
funs1 = 
   [ ("haakjes", haakjes), ("len", len), ("val1", val1), ("prop", prop), ("val2", val2)
   , ("bin", bin), ("valb", valB), ("vala", valA), ("nnf", nnf)
   , ("star5", star5), ("lengte", lengte), ("rev", rev), ("val", val)
   , ("nneg", nneg), ("star", star), ("stari", stari), ("impl", impl), ("subf", subf)
   , ("g", funG), ("supp", supp)
   ]

funs2 :: [(String, Expr -> Expr -> Expr)]
funs2 = [("min", minm), ("max", maxm), ("union", union), ("del", del)]

funs3 :: [(String, Expr -> Expr -> Expr -> Expr)]
funs3 = [("subst", subst)]

exprTable :: [[Operator Char () Expr]]
exprTable =
   [ -- precedence level 7
     [ Infix ((^) <$ reservedOp "^") AssocRight
     ]
     -- precedence level 7
   , [ Infix ((*) <$ reservedOp "*") AssocLeft
     , Infix ((/) <$ reservedOp "/") AssocLeft
     ]
     -- precedence level 6+
   , [ Prefix (negate <$ reservedOp "-")
     ]
     -- precedence level 6
   , [ Infix ((+) <$ reservedOp "+") AssocLeft
     , Infix ((-) <$ reservedOp "-") AssocLeft
     ]
     
   -- not symbol (~) is parsed by factor, to allow expressions such as ~~p
   -- , [ Prefix (complement <$ reservedOp "~") ]
     -- presedence level 3
   , [ Infix ((<&&>) <$ reservedOp "&&") AssocRight ]
     -- presedence level 2
   , [ Infix ((<||>) <$ reservedOp "||") AssocRight ]
   , [ Infix ((<->>) <$ reservedOp "->") AssocRight ]
   ]

--------------------------------------------------------------------------
-- Lexing

lexer :: P.TokenParser a
lexer = P.makeTokenParser $ emptyDef
   { reservedNames   = vars ++ map fst cons ++ map fst funs ++ map fst funs1 ++ map fst funs2 ++ map fst funs3
   , reservedOpNames = ["->", "~", "==", "/=", "<=", ">=", "<", ">", "~=", "+", "-", "*", "^", "/"]
   , opStart         =  oneOf ":!#$%&*+./<=>?@\\^|-~"
   , opLetter        =  oneOf ":!#$%&*+./<=>?@\\^|-" -- but not ~
   }

identifier :: Parser String
identifier = P.identifier lexer

natural :: Parser Integer
natural = P.natural lexer

reserved :: String -> Parser ()
reserved = P.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer

comma :: Parser String
comma = P.comma lexer

parens :: Parser a -> Parser a
parens = P.parens lexer