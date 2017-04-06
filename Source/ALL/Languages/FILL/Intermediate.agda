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
{-# COMPILED_DATA IPattern IPattern PTriv Block PVar PTensor PPar #-}

data ITerm : Set where
  Triv : ITerm
  Void : ITerm
  TTensor : ITerm -> ITerm -> ITerm
  TPar : ITerm -> ITerm -> ITerm
  Lam : String -> Type -> ITerm -> ITerm
  Let : ITerm -> Type -> IPattern -> ITerm -> ITerm
  App : ITerm -> ITerm -> ITerm
{-# COMPILED_DATA ITerm ITerm Triv Void TTensor TPar Lam Let App #-}

