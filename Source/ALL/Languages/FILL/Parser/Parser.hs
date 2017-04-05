{-# 
LANGUAGE 
  NoMonomorphismRestriction, 
  PackageImports, 
  TemplateHaskell, 
  FlexibleContexts 
#-}

module Languages.FILL.Parser.Parser where

import Prelude hiding (True)
import Text.Parsec hiding (Empty)
import Text.Parsec.Expr

import Languages.FILL.TypeSyntax
import Languages.FILL.Interface
import qualified Languages.FILL.Parser.Tokenizer as Tok

constParser p c = p >> return c

binaryOp p b op = do
  x <- p
  b
  y <- p
  return $ op x y

binOp assoc op f = Text.Parsec.Expr.Infix (do{ op;return f}) assoc

typeTable = [[binOp AssocNone  tensorParser (\d r -> Tensor d r)],
             [binOp AssocNone  parParser (\d r -> Par d r)],           
             [binOp AssocRight impParser (\d r -> Imp d r)]]

typeParser = buildExpressionParser typeTable typeParser'
typeParser' = try (Tok.parens typeParser) <|> topParser <|> bottomParser

impParser = constParser Tok.linImp Imp
tensorParser = constParser Tok.tensor Tensor
parParser = constParser Tok.par Par
topParser = constParser Tok.top Top
bottomParser = constParser Tok.bottom Bottom

patternTable = [[binOp AssocNone  ptensorParser (\d r -> PTensor d r)],
                [binOp AssocNone  pparParser (\d r -> PPar d r)]]   

patternParser = buildExpressionParser patternTable patternParser'
patternParser' = try (Tok.parens patternParser) <|> blockParser <|> trivParser

blockParser = constParser (Tok.symbol '-') Block
trivParser = constParser (Tok.triv) PTriv
ptensorParser = constParser Tok.tensor PTensor
pparParser = constParser Tok.par PPar
                
expr' = try (Tok.parens expr) <|> lamParser <|> letParser <|> voidParser <|> varParser 

expr = buildExpressionParser tOpTable expr'
 where
   tOpTable = [[binOp AssocNone  ttensorParser (\d r -> TTensor d r)],
               [binOp AssocNone  tparParser (\d r -> TPar d r)]]   

ttensorParser = constParser Tok.tensor TTensor
tparParser = constParser Tok.par TPar

varParser = do
  x <- Tok.var
  return $ Var x

voidParser = constParser Tok.void Void             
             
lamParser = do
  Tok.symbol '\\'
  x <- Tok.var
  Tok.symbol ':'
  ty <- typeParser
  Tok.symbol '.'
  b <- expr
  return $ Lam x ty b

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