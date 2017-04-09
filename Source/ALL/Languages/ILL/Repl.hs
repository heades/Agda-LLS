{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Languages.ILL.Repl where

import Control.Monad.State
import System.Console.Haskeline
import System.Console.Haskeline.MonadException    
import System.Exit
import System.FilePath
import qualified Data.Map.Strict as M

import Utils.Queue
import Utils.Exception
import Languages.ILL.Intermediate
import Languages.ILL.TypeSyntax
import Languages.ILL.Parser.Parser
import Languages.ILL.Pretty
import MAlonzo.Code.Languages.ILL.AgdaInterface

type Qelm = (IName, ITerm)
type REPLStateIO = StateT (FilePath,Queue (QDefName, QDefDef)) IO

instance MonadException m => MonadException (StateT (FilePath,Queue (QDefName, QDefDef)) m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'                       

data QDefName = DefVar IName | DefName IName
    deriving (Show, Eq)
data QDefDef  = DefTerm ITerm | VarType Type
    deriving Show

getQDefM :: (QDefName, QDefDef) -> REPLStateIO (Either (IName, Type) (IName, ITerm))
getQDefM e@(DefVar x, DefTerm t) = return $ Right (x , t)
getQDefM e@(DefName x, VarType ty) = return $ Left (x , ty)
getQDefM e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "++(prettyDef e)

getQDef :: (QDefName, QDefDef) -> Either (IName, Type) (IName, ITerm)
getQDef e@(DefVar x, DefTerm t) = Right (x , t)
getQDef e@(DefName x, VarType ty) = Left (x , ty)
getQDef e@(x,y) = error $ "Failed to get definition from context. Mismatched variable and type or term in: "++(prettyDef e)

-- Extract only free variables that are defined from queue
getQFVM :: Queue (QDefName,QDefDef) -> Queue (IName,Type) -> REPLStateIO (Queue (IName,Type))
getQFVM (Queue [] []) qFV = return $ qFV
getQFVM q qFV = getQDefM (headQ q) >>= (\x -> case x of
                 (Left fv) -> getQFVM (tailQ q) (enqueue fv qFV)
                 (Right cv) -> getQFVM (tailQ q) qFV)

-- Extract only closed terms from queue
getQCTM :: Queue (QDefName,QDefDef) -> Queue Qelm -> REPLStateIO (Queue Qelm)
getQCTM (Queue [] []) qCV = return $ qCV
getQCTM q qCV = getQDefM (headQ q) >>= (\x -> case x of 
                 (Left fv) -> getQCTM (tailQ q) qCV
                 (Right cv) -> getQCTM (tailQ q) (enqueue cv qCV))
                 
-- Extract only free variables that are defined from queue, non-monadic version
getQFV :: Queue (QDefName,QDefDef) -> Queue (IName,Type) -> (Queue (IName,Type))
getQFV (Queue [] []) qFV = qFV
getQFV q qFV = case getQDef (headQ q) of
                 (Left fv) -> getQFV (tailQ q) (enqueue fv qFV)
                 (Right cv) -> getQFV (tailQ q) qFV

-- Extract only closed terms from queue, non-monadic version
getQCT :: Queue (QDefName,QDefDef) -> Queue Qelm -> (Queue Qelm)
getQCT (Queue [] []) qCV = qCV
getQCT q qCV = case getQDef (headQ q) of 
                 (Left fv) -> getQCT (tailQ q) qCV
                 (Right cv) -> getQCT (tailQ q) (enqueue cv qCV)
                 
qToMap :: Queue (IName,Type) -> (M.Map IName Type)
qToMap q = foldl (\m (a,b) -> M.insert a b m) M.empty (toListQ q)
                
io :: IO a -> REPLStateIO a
io i = liftIO i
    
pop :: REPLStateIO (QDefName, QDefDef)
pop = get >>= return.headQ.snd

push :: (QDefName, QDefDef) -> REPLStateIO ()
push t = do
  (f,q) <- get
  put (f,(q `snoc` t))

set_wdir :: FilePath -> REPLStateIO ()
set_wdir wdir = do
  (_,q) <- get
  put (wdir,q)         
     
-- unfoldDefsInTerm :: (Queue Qelm) -> ITerm -> ITerm
-- unfoldDefsInTerm q t =
--     let uq = toListQ $ unfoldQueue q
--      in substs uq t

-- unfoldQueue :: (Queue Qelm) -> (Queue Qelm)
-- unfoldQueue q = fixQ q emptyQ step
--  where
--    step :: (Name ITerm, ITerm) -> t -> Queue Qelm -> Queue Qelm
--    step e@(x,t) _ r = (mapQ (substDef x t) r) `snoc` e
--     where
--       substDef :: Name ITerm -> ITerm -> Qelm -> Qelm
--       substDef x t (y, t') = (y, subst x t t')
      
-- containsTerm :: Queue (QDefName,QDefDef) -> QDefName -> Bool
-- containsTerm (Queue [] []) _ = False
-- containsTerm q v = (containsTerm_Qelm (getQCT q emptyQ) v) || (containsTerm_QFV (getQFV q emptyQ) v)

-- containsTerm_Qelm :: Queue Qelm -> QDefName -> Bool
-- containsTerm_Qelm (Queue f r) v@(Var vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))
-- containsTerm_Qelm (Queue f r) v@(DefName vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))

-- containsTerm_QFV :: Queue (IName, Type) -> QDefName -> Bool
-- containsTerm_QFV (Queue f r) v@(Var vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))
-- containsTerm_QFV (Queue f r) v@(DefName vnm) = ((foldl (\b (defName, defTerm)-> b || (vnm == defName)) False r) || (foldl (\b (defName, defTerm)-> b || (vnm == defName)) False  f ))
 
-- tyCheckQ :: GFile -> REPLStateIO ()
-- tyCheckQ (Queue [] []) = return () 
-- tyCheckQ q = do
--   (f, defs') <- get
--   defs <- getQCTM defs' emptyQ
--   qfv <- getQFVM defs' emptyQ
--   let term'@(Def v ty t) = headQ q
--   -- Case split here as well before unfolding t
--   -- Unfold each term from queue and see if free variables exist
--   let tu = unfoldDefsInTerm defs t
--   let numFV = length (getFV tu)
--   if (numFV == 0)
-- -- TypeCheck term from Prog
--   then let r = runIR tu $ qToMap qfv   
--       in case r of
--            Left err -> io.putStrLn.readTypeError $ err
--                 -- Verify type from TypeChecker matches expected type from file
--                 -- If it does, add to context (i.e. definition queue)
--            Right ity ->
--                do
--                   case ity `isSubtype` ty of
--                     Left er -> io.putStrLn.readTypeError $ er
--                     Right b -> 
--                         if b
--                         then do
--                           -- Determine if definition already in queue
--                           if(containsTerm defs' (Var v))
--                           then  io.putStrLn $ "Error: The variable "++(show v)++" is already in the context."
--                           else  do
--                             push (Var v,DefTerm tu)
--                             tyCheckQ $ tailQ q
--                         else io.putStrLn $ "Error: "++(runPrettyType ity)++" is not a subtype of "++(runPrettyType ty)
--   else io.putStrLn $ "Error: free variables found in "++(show v)

handleCMD :: String -> REPLStateIO ()
handleCMD "" = return ()
handleCMD s =    
    case (parseLine s) of
      Left msg -> io $ putStrLn msg
      Right l -> handleLine l
  where    
--     handleLine (Eval t) = do
--       (f, defs') <- get
--       defs <- getQCTM defs' emptyQ
--       let tu = unfoldDefsInTerm defs t
--           r = eval tu
--        in case r of
--             Left m -> io.putStrLn.readTypeError $ m
--             Right e -> io.putStrLn.runPrettyITerm $ e
--     handleLine (DecVar vnam ty) = do
--       (f, defs) <- get
--       if(containsTerm defs (DefName vnam))
--         then io.putStrLn $ "error: The name "++(show vnam)++" is already in the context."
--         else push (DefName vnam,VarType ty)
--     handleLine (Let x t) = do
--       (f, defs') <- get
--       defs <- getQCTM defs' emptyQ
--       qfv <- getQFVM defs' emptyQ
--       let tu = unfoldDefsInTerm defs t
--           r = runIR tu $ qToMap qfv
--        in case r of
--             Left m -> io.putStrLn.readTypeError $ m
--             Right ty ->  do
--                 if(containsTerm defs' (Var x))
--                 then io.putStrLn $ "error: The variable "++(show x)++" is already in the context."
--                 else push (Var x,DefTerm t)
    handleLine (TypeCheck t) = do
      (_, defs') <- get
      --defs <- getQCTM defs' emptyQ
      --qfv <- getQFVM defs' emptyQ
      let tu = t --unfoldDefsInTerm defs t
          r = runTypeCheck tu
       in case r of
            Left m -> io.putStrLn.show $ m
            Right ty ->  io.putStrLn.prettyType $ ty
    handleLine (ShowAST t) = do
      (_,defs') <- get
      defs <- getQCTM defs' emptyQ
      io.putStrLn.show $ t --unfoldDefsInTerm defs t
--     handleLine (Unfold t) = do
--       (f,defs') <- get
--       defs <- getQCTM defs' emptyQ
--       io.putStrLn.runPrettyITerm $ unfoldDefsInTerm defs t
--     handleLine (LoadFile p) = do
--       let wdir = takeDirectory p
--       let file = takeFileName p
--       if (not (null wdir))
--       then do
--         set_wdir wdir
--         loadFile file
--       else loadFile file
--     handleLine DumpState = get >>= io.print.(mapQ prettyDef).snd
     
prettyDef :: (QDefName, QDefDef) -> String
prettyDef elem = case getQDef elem of
                   Right (a, t) -> "let "++(n2s a)++" = "++(prettyTerm t)
                   Left (a, ty ) -> (n2s a)++" : "++(prettyType ty)

-- loadFile :: FilePath -> REPLStateIO ()
-- loadFile p = do
--   (wdir,_) <- get
--   -- delete definitions currently in queue, this allows reloading the same file after making changes
--   put (wdir,emptyQ)         
--   msgOrGFile <- lift $ runFileParser p wdir
--   case msgOrGFile of
--     Left l -> io.putStrLn $ l
--     Right r -> tyCheckQ r
   
-- getFV :: ITerm -> [IName]
-- getFV t = fv t :: [IName]

helpMenu :: String                          
helpMenu = 
      "-----------------------------------------------------------------------------------\n"++
      "                  The ALL Menu                                                     \n"++
      "-----------------------------------------------------------------------------------\n"++
      ":help             (:h)  Display the help menu\n"++
      ":type term        (:t)  Typecheck a term\n"++
      ":show <term>      (:s)  Display the Abstract Syntax Type of a term\n"++
      ":unfold <term>    (:u)  Unfold the expression into one without toplevel definition.\n"++ 
      ":dump             (:d)  Display the context\n"++
      "load <filepath>   (:l)  Load an external file into the context\n"++
      "-----------------------------------------------------------------------------------"
          
repl :: IO ()
repl = do
  evalStateT (runInputT defaultSettings loop) ("",emptyQ)
   where 
       loop :: InputT REPLStateIO ()
       loop = do           
           minput <- getInputLine "ILL> "
           case minput of
               Nothing -> return ()
               Just [] -> loop
               Just input | input == ":q" || input == ":quit"
                              -> liftIO $ putStrLn "Leaving ALL." >> return ()
                          | input == ":h" || input == ":help"
                              -> (liftIO $ putStrLn helpMenu) >> loop                                 
                          | otherwise -> (lift.handleCMD $ input) >> loop