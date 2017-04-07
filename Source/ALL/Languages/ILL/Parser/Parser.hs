{-# LANGUAGE NoMonomorphismRestriction #-}

module Languages.ILL.Parser.Parser where

import Prelude hiding (True)
import Data.Char
import Data.Text
import Text.Parsec hiding (Empty)
import Text.Parsec.Expr

import Languages.ILL.TypeSyntax
import Languages.ILL.Intermediate
import qualified Languages.ILL.Parser.Tokenizer as Tok

constParser p c = p >> return c

binOp assoc op f = Text.Parsec.Expr.Infix (do{ op;return f}) assoc

reservedWords = ["Top", "let", "in", "be", "triv", "discard",
                 "of", "copy", "derelicit", "as", "promote", "for"]
                                                           
typeParser = buildExpressionParser typeTable typeParser'
 where
   typeTable = [[binOp AssocNone  tensorParser (\d r -> Tensor d r)],
                [binOp AssocRight impParser (\d r -> Imp d r)]]
typeParser' = try (Tok.parens typeParser) <|> topParser <|> bangParser <|> tyvarParser

tyvarParser = do
  x <- Tok.var
  if isLower $ Prelude.head $ x
  then fail "Type variables must begin with an uppercase letter."
  else if x `elem` reservedWords
       then fail $ x ++ " is a reserved word."
       else return $ TVar $ pack x

impParser = constParser Tok.linImp Imp
tensorParser = constParser Tok.tensor Tensor
topParser = constParser Tok.top Top
bangParser = (Tok.symbol '!') >> typeParser >>= (\ty -> return $ Bang ty)

patternParser = try (Tok.parens patternParser) <|> try ptrivParser <|> ptensorParser <|> pvarParser
                
pvarParser = do
  x <- varNameParser
  return $ PVar x

ptrivParser = constParser (Tok.triv) PTriv
ptensorParser = do
  x <- pvarParser
  Tok.tensor
  y <- pvarParser
  return $ PTensor x y

expr = buildExpressionParser tOpTable expr'
 where
   tOpTable = [[binOp AssocNone  ttensorParser (\d r -> TTensor d r)]]   
aterm = try (Tok.parens expr) <|> trivParser <|> varParser 
expr' = lamParser <|> letParser <|> promoteParser <|> discardParser <|> copyParser <|> derelictParser <|> appParser
              
ttensorParser = constParser Tok.tensor TTensor
trivParser = constParser Tok.triv Triv

varNameTypeParser = do
  x <- varNameParser
  Tok.symbol ':'
  ty <- typeParser
  return (x , ty)

promoteParser = do
  Tok.promote
  ms <- expr `sepBy` (Tok.symbol ',')
  Tok.forT
  xs <- varNameTypeParser `sepBy` (Tok.symbol ',')
  Tok.inT
  n <- expr
  return $ Promote ms xs n

discardParser = do
  Tok.discard
  m <- expr
  Tok.inT
  n <- expr
  return $ Discard m n

copyParser = do
  Tok.copy
  m <- expr
  Tok.asT
  x <- varNameParser
  Tok.symbol ','
  y <- varNameParser
  Tok.inT
  n <- expr
  return $ Copy m x y n

derelictParser = do
  Tok.derelict
  m <- expr
  return $ Derelict m

appParser = do  
  t <- many aterm
  case t of
    [] -> fail "Empty application is not supported: must supply a term."
    _ -> return $ Prelude.foldl1 App t
             
varNameParser = do
  x <- Tok.var
  if isUpper $ Prelude.head x
  then fail "Variables must begin with a lowercase letter."
  else if x `elem` reservedWords
       then fail $ x ++ " is a reserved word."
       else return $ pack x

varParser = do
  x <- varNameParser
  return $ Var x
            
lamParser = do
  Tok.symbol '\\'
  x <- Tok.var
  Tok.symbol ':'
  ty <- typeParser
  Tok.symbol '.'
  b <- expr
  return $ Lam (pack x) ty b

letParser = do
  Tok.leT
  a <- expr
  Tok.symbol ':'
  ty <- typeParser
  Tok.be
  p <- patternParser
  Tok.inT
  t <- expr
  return $ Let a ty p t
