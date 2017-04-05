{
module Languages.FILL.Parser.Token (ALLTok(..), Token(..), getTokens, AlexPosn(..)) where
}

%wrapper "posn"

$digit = 0-9      
$alpha = [a-zA-Z] 

tokens :-
  $white+                       ;
  "--".*                        ;
  let                           { \p _ -> (Let, p)         }
  [\=\+\-\*\/\(\)]              { \p s -> (Sym (head s),p) }
  $alpha [$alpha $digit \_ \']* { \p s -> (Var s,p)        }
  "-o"                          { \p _ -> (LinImp, p)      }
  "(x)"                         { \p _ -> (Tensor, p)      }
  "(+)"                         { \p _ -> (Par, p)         }
  "False"                       { \p _ -> (Bottom, p)      }
  "True"                        { \p _ -> (Top, p)         }
  "Triv"                        { \p _ -> (Triv, p)        }
  "void"                        { \p _ -> (Void, p)        }
{
-- Each right-hand side has type :: String -> Token
-- The token type:
data ALLTok = Par
            | Tensor
            | LinImp 
            | Triv 
            | Bottom 
            | Top 
            | Void 
            | Let 
            | Sym Char 
            | Var String
    deriving (Eq,Show)

type Token = (ALLTok, AlexPosn)
    
position :: Token -> AlexPosn
position = snd

getTokens :: String -> [Token]
getTokens str = alexScanTokens str
}
