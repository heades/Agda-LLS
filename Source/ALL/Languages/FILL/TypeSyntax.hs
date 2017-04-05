{-# 
LANGUAGE 
  FlexibleInstances, 
  TemplateHaskell, 
  MultiParamTypeClasses, 
  UndecidableInstances 
#-}
module Languages.FILL.TypeSyntax where

data Type = TVar String
          | Top          
          | Bottom
          | Imp Type Type
          | Tensor Type Type
          | Par Type Type
 deriving (Show, Eq)
