{-# 
LANGUAGE 
  FlexibleInstances, 
  TemplateHaskell, 
  MultiParamTypeClasses, 
  UndecidableInstances 
#-}
module Languages.FILL.TypeSyntax where

import Data.Text
    
data Type = TVar Text
          | Top          
          | Bottom
          | Imp Type Type
          | Tensor Type Type
          | Par Type Type
 deriving (Show, Eq)
