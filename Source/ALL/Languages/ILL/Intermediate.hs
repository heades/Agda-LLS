-- Below are the data types for passing information from the 
-- Haskell front end to the Agda back end.  Both sides must
-- implement these data types.

module Languages.ILL.Intermediate where
                  
import Data.Text

import Languages.ILL.TypeSyntax

type IName = Text

data ITerm = Var IName
           | Triv
           | TTensor ITerm ITerm
           | Lam IName Type ITerm
           | Let ITerm Type IPattern ITerm
           | App ITerm ITerm
           | Promote [(ITerm,IName,Type)] ITerm
           | Discard ITerm ITerm
           | Copy ITerm IName IName ITerm
           | Derelict ITerm
 deriving Show
        
data IPattern = PTriv
              | PVar IName
              | PTensor  IPattern IPattern
 deriving Show
        
n2s :: IName -> String
n2s = unpack