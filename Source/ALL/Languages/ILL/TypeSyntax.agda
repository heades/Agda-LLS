module Languages.ILL.TypeSyntax where

open import bool

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

_eq-type_ : Type → Type → 𝔹
(TVar _) eq-type (TVar _) = tt
Top eq-type Top = tt
(Imp A C) eq-type (Imp B D) = (A eq-type B) && (C eq-type D)
(Tensor A C) eq-type (Tensor B D) = (A eq-type B) && (C eq-type D)
(Bang A) eq-type (Bang B) = A eq-type B
_ eq-type _ = ff
