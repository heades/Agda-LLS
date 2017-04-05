{-# 
LANGUAGE 
  FlexibleInstances, 
  TemplateHaskell, 
  MultiParamTypeClasses, 
  UndecidableInstances 
#-}
module Languages.FILL.TypeSyntax where

data Type = Top
          | Bottom
          | Imp Type Type
          | Tensor Type Type
          | Par Type Type
 deriving (Show, Eq)
