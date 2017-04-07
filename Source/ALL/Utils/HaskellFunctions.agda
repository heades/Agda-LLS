module Utils.HaskellFunctions where

open import bool

open import Utils.HaskellTypes

postulate _str-eq_ : String → String → 𝔹
{-# COMPILED _str-eq_ (==) #-}

infixr 20 _++s_
postulate _++s_ : String → String → String
{-# COMPILED _++s_ Data.Text.append #-}
