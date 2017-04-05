module Languages.FILL.Parser.Tokenizer where

import Text.Parsec
import Languages.FILL.Parser.Token

satisfy f = tokens _ _