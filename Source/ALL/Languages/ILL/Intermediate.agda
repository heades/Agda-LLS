module Languages.ILL.Intermediate where

open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Languages.ILL.TypeSyntax

{-# IMPORT Languages.ILL.Intermediate #-}

data IPattern : Set where
  PTriv : IPattern
  PVar : String → IPattern
  PTensor : IPattern → IPattern → IPattern
{-# COMPILED_DATA IPattern Languages.ILL.Intermediate.IPattern 
                           Languages.ILL.Intermediate.PTriv 
                           Languages.ILL.Intermediate.PVar 
                           Languages.ILL.Intermediate.PTensor #-}

data ITerm : Set where
  Var : String → ITerm
  Triv : ITerm
  TTensor : ITerm → ITerm → ITerm
  Lam : String → Type → ITerm → ITerm
  Let : ITerm → Type → IPattern → ITerm → ITerm
  App : ITerm → ITerm → ITerm
  Promote : List (Triple ITerm String Type) → ITerm → ITerm
  Discard : ITerm → ITerm → ITerm
  Copy : ITerm → String → String → ITerm → ITerm
  Derelict : ITerm → ITerm
{-# COMPILED_DATA ITerm Languages.ILL.Intermediate.ITerm 
                        Languages.ILL.Intermediate.Var
                        Languages.ILL.Intermediate.Triv 
                        Languages.ILL.Intermediate.TTensor 
                        Languages.ILL.Intermediate.Lam 
                        Languages.ILL.Intermediate.Let 
                        Languages.ILL.Intermediate.App 
                        Languages.ILL.Intermediate.Promote
                        Languages.ILL.Intermediate.Discard
                        Languages.ILL.Intermediate.Copy
                        Languages.ILL.Intermediate.Derelict #-}
