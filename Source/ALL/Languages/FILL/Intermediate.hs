-- Below are the data types for passing information from the 
-- Haskell front end to the Agda back end.  Both sides must
-- implement these data types.

module Languages.FILL.Intermediate (ITerm(..),
                                    IPattern(..)) where
                  
import Languages.FILL.TypeSyntax

data ITerm = Var String
           | Triv
           | Void
           | TTensor ITerm ITerm
           | TPar ITerm ITerm
           | Lam String Type ITerm
           | Let ITerm Type IPattern ITerm
           | App ITerm ITerm
 deriving Show
        
data IPattern = PTriv
              | Block
              | PVar String
              | PTensor  IPattern IPattern
              | PPar    IPattern IPattern   
 deriving Show
        
