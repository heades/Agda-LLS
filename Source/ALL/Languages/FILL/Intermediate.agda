module Languages.FILL.Intermediate where

open import Utils.HaskellTypes
open import Languages.FILL.TypeSyntax

{-# IMPORT Languages.FILL.Intermediate #-}

data IPattern : Set where
  PTriv : IPattern
  Block : IPattern
  PVar : String -> IPattern
  PTensor : IPattern -> IPattern -> IPattern
  PPar : IPattern -> IPattern -> IPattern
{-# COMPILED_DATA IPattern Languages.FILL.Intermediate.IPattern 
                           Languages.FILL.Intermediate.PTriv 
                           Languages.FILL.Intermediate.Block 
                           Languages.FILL.Intermediate.PVar 
                           Languages.FILL.Intermediate.PTensor 
                           Languages.FILL.Intermediate.PPar #-}

data ITerm : Set where
  Triv : ITerm
  Void : ITerm
  TTensor : ITerm -> ITerm -> ITerm
  TPar : ITerm -> ITerm -> ITerm
  Lam : String -> Type -> ITerm -> ITerm
  Let : ITerm -> Type -> IPattern -> ITerm -> ITerm
  App : ITerm -> ITerm -> ITerm
{-# COMPILED_DATA ITerm Languages.FILL.Intermediate.ITerm 
                        Languages.FILL.Intermediate.Triv 
                        Languages.FILL.Intermediate.Void 
                        Languages.FILL.Intermediate.TTensor 
                        Languages.FILL.Intermediate.TPar 
                        Languages.FILL.Intermediate.Lam 
                        Languages.FILL.Intermediate.Let 
                        Languages.FILL.Intermediate.App #-}
