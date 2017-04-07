module ExampleHStoAgdaAndBack where

import Text.Parsec hiding (Empty)    
    
import qualified Languages.FILL.Parser.Tokenizer as Tok
import Languages.FILL.Intermediate
import Languages.FILL.Parser.Parser
import MAlonzo.Code.Languages.FILL.AgdaInterface
import Utils.Exception

test :: String -> Either Exception ITerm
test s = case x of
           Left m -> error.show $ m
           Right t -> transUntransId t
 where
   x = (parse expr "").(Tok.getTokens) $ s