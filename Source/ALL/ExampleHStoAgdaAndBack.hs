module ExampleHStoAgdaAndBack where

import Text.Parsec hiding (Empty)    
    
import qualified Languages.ILL.Parser.Tokenizer as Tok
import Languages.ILL.Intermediate
import Languages.ILL.Parser.Parser
import MAlonzo.Code.Languages.ILL.AgdaInterface
import Utils.Exception

test :: String -> Either Exception ITerm
test s = case x of
           Left m -> error.show $ m
           Right t -> transUntransId t
 where
   x = (parse expr "").(Tok.getTokens) $ s