{-# LANGUAGE FlexibleContexts #-}
module Languages.FILL.Parser.Tokenizer (module Languages.FILL.Parser.Token,
                                        triv,
                                        inT,
                                        be,
                                        void,
                                        tensor,
                                        par,
                                        linImp,
                                        top,
                                        bottom,
                                        leT,
                                        symbol,
                                        var,
                                        parens) where

import Text.Parsec hiding (satisfy)
import Languages.FILL.Parser.Token

satisfy :: Monad m => (Token -> Maybe a) -> ParsecT [Token] u m a
satisfy = tokenPrim show next_pos
 where
   next_pos :: SourcePos -> Token -> [Token] -> SourcePos
   next_pos p _ [] = p
   next_pos p _ ((_, AlexPn _ l c):_) = setSourceColumn (setSourceLine p l) c

constParser :: Monad m => ALLTok -> ParsecT [Token] u m ()
constParser t = satisfy p <?> show t
 where   
   p (t',_) | t == t' = Just ()
   p _ = Nothing

triv :: Monad m => ParsecT [Token] u m ()
triv = constParser Triv

inT :: Monad m => ParsecT [Token] u m ()
inT = constParser In

be :: Monad m => ParsecT [Token] u m ()
be = constParser Be
      
void :: Monad m => ParsecT [Token] u m ()
void = constParser Void

tensor :: Monad m => ParsecT [Token] u m ()
tensor = constParser Tensor

par :: Monad m => ParsecT [Token] u m ()
par = constParser Par

linImp :: Monad m => ParsecT [Token] u m ()
linImp = constParser LinImp

top :: Monad m => ParsecT [Token] u m ()
top = constParser Top

bottom :: Monad m => ParsecT [Token] u m ()
bottom = constParser Bottom

leT :: Monad m => ParsecT [Token] u m ()
leT = constParser Let

symbol :: Monad m => Char -> ParsecT [Token] u m Char
symbol s = satisfy p <?> show s
 where   
   p (Sym s',_) | s == s' = Just s
   p _ = Nothing

var :: Monad m => ParsecT [Token] u m String
var = satisfy p <?> "variable"
 where   
   p (Var s,_) = Just s
   p _ = Nothing

parens :: Monad m => ParsecT [Token] u m a -> ParsecT [Token] u m a
parens pr = do
  symbol '('
  x <- pr
  symbol ')'
  return x