-- Below are the data types for passing information from the 
-- Haskell front end to the Agda back end.  Both sides must
-- implement these data types.

module Interface (ITerm(..),
                  IPattern(..)) where
                  
import TypeSyntax
                  
data ITerm = Var String
           | Triv
           | Void
           | Tensr ITerm ITerm
           | Par ITerm ITerm
           | Lam String Type ITerm
           | Let ITerm Type IPattern ITerm    
        deriving Show
        
data IPattern = 
        PTriv                        |
        Block                       |
        PVar String                  |
        PTensr  IPattern IPattern   |
        PPar    IPattern IPattern   
        deriving Show
        
