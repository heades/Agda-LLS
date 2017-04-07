{
module Languages.ILL.Parser.Token (ALLTok(..), Token(..), getTokens, AlexPosn(..)) where
}

%wrapper "posn"

$digit = 0-9      
$alpha = [a-zA-Z] 
@var = $alpha [$alpha $digit \_ \']*

tokens :-
  $white+                       ;
  "--".*                        ;
  let                           { \p _ -> (Let, p)           }
  in                            { \p _ -> (In, p)            }
  be                            { \p _ -> (Be, p)            }
  of                            { \p _ -> (Of, p)            }
  as                            { \p _ -> (As, p)            }
  discard                       { \p _ -> (Discard, p)       }
  copy                          { \p _ -> (Copy, p)          }
  derelict                      { \p _ -> (Derelict, p)    }
  promote                       { \p _ -> (Promote, p)       }
  for                           { \p _ -> (For, p)       }
  [\!\,\=\+\*\/\(\)\.:\\]       { \p s -> (Sym (head s), p)  }  
  "-o"                          { \p _ -> (LinImp, p)        }
  "(x)"                         { \p _ -> (Tensor, p)        }
  "(+)"                         { \p _ -> (Par, p)           }
  "False"                       { \p _ -> (Bottom, p)        }
  "True"                        { \p _ -> (Top, p)           }
  "triv"                        { \p _ -> (Triv, p)          }
  "void"                        { \p _ -> (Void, p)          }
  @var                          { \p s -> (Var s,p)          }
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
            | In
            | Be
            | Sym Char 
            | Var String
            | Discard
            | Of
            | Copy
            | Derelict
            | As
            | Promote
            | For
    deriving (Eq,Show)

type Token = (ALLTok, AlexPosn)
    
position :: Token -> AlexPosn
position = snd

getTokens :: String -> [Token]
getTokens str = alexScanTokens str
}
