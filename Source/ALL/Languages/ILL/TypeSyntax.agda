module Languages.ILL.TypeSyntax where

open import Utils.HaskellTypes

{-# IMPORT Languages.ILL.TypeSyntax #-}

data Type : Set where
  TVar : String → Type
  Top : Type
  Imp : Type → Type → Type
  Tensor : Type → Type → Type
  Bang : Type → Type

{-# COMPILED_DATA Type Languages.ILL.TypeSyntax.Type 
                       Languages.ILL.TypeSyntax.TVar 
                       Languages.ILL.TypeSyntax.Top 
                       Languages.ILL.TypeSyntax.Imp 
                       Languages.ILL.TypeSyntax.Tensor
                       Languages.ILL.TypeSyntax.Bang #-}
