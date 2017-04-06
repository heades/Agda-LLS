module Languages.FILL.TypeSyntax where

open import Utils.HaskellTypes

{-# IMPORT Languages.FILL.TypeSyntax #-}

data Type : Set where
  TVar : String → Type
  Top : Type
  Bottom : Type
  Imp : Type → Type → Type
  Tensor : Type → Type → Type
  Par : Type → Type → Type

{-# COMPILED_DATA Type Type TVar Top Bottom Imp Tensor Par #-}
