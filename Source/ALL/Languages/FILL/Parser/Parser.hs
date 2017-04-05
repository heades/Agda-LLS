{-# 
LANGUAGE 
  NoMonomorphismRestriction, 
  PackageImports, 
  TemplateHaskell, 
  FlexibleContexts 
#-}

module Languages.FILL.Parser.Parser where

import Prelude
import Data.List
import Data.Char 
import qualified Data.Text as T
import Text.Parsec hiding (Empty)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
import Control.Monad -- For debugging messages.
import Data.Functor.Identity
import Text.Parsec.Extra
import System.FilePath
import System.Directory

import Languages.FILL.Interface

type Parser a = Parsec [Token] a
type ParserT u m a = ParsecT [Token] u m a    

