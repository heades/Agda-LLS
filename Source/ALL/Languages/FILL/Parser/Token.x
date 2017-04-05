{
module Languages.FILL.Parser.Token (Token(..), getTokens) where
}

%wrapper "basic"

$digit = 0-9            -- digits
$alpha = [a-zA-Z]       -- alphabetic characters

tokens :-

  $white+               ;
  "--".*                { \s -> Comment }
  let                   { \s -> Let }
  $digit+               { \s -> Int (read s) }
  [\=\+\-\*\/\(\)]      { \s -> Sym (head s) }
  $alpha [$alpha $digit \_ \']*     { \s -> Var s }
  "-o"                  { \s -> LinImp }
  "(x)"                 { \s -> Tnsr }
  "(+)"                 { \s -> Par }
  "False"               { \s -> Bttm }
  "True"                { \s -> Top }
  "Triv"                { \s -> Triv }
  "o"                   { \s -> Void }
{
-- Each right-hand side has type :: String -> Token
-- The token type:
data Token =
    White       |
    Comment     |
    Par         |
    Tnsr        |
    LinImp      |
    Triv        |
    Bttm        |
    Top         |
    Void        |
    Let         |
    Sym Char    |
    Var String  |
    Int Int     |
    Err 
    deriving (Eq,Show)
    
getTokens :: String -> [Token]
getTokens str = alexScanTokens str
}
