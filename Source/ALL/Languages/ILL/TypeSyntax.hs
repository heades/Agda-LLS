module Languages.ILL.TypeSyntax where

import Data.Text
    
data Type = TVar Text
          | Top          
          | Imp Type Type
          | Tensor Type Type
          | Bang Type
 deriving (Show, Eq)
