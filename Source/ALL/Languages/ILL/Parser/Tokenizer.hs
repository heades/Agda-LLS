{-# LANGUAGE FlexibleContexts #-}
module Languages.ILL.Parser.Tokenizer (module Languages.ILL.Parser.Token,
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
                                        parens,
                                        promote,
                                        forT,
                                        discard,
                                        copy,
                                        asT,
                                        derelict) where

import Text.Parsec hiding (satisfy)
import Languages.ILL.Parser.Token

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

ofT :: Monad m => ParsecT [Token] u m ()
ofT = constParser Of

discard :: Monad m => ParsecT [Token] u m ()
discard = constParser Discard

copy :: Monad m => ParsecT [Token] u m ()
copy = constParser Copy

derelict :: Monad m => ParsecT [Token] u m ()
derelict = constParser Derelict

promote :: Monad m => ParsecT [Token] u m ()
promote = constParser Promote

asT :: Monad m => ParsecT [Token] u m ()
asT = constParser As

forT :: Monad m => ParsecT [Token] u m ()
forT = constParser For      

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