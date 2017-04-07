module Utils.HaskellFunctions where

open import bool

open import Utils.HaskellTypes

postulate _str-eq_ : String → String → 𝔹

{-# COMPILED _str-eq_ (==) #-}
