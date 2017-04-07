module Utils.HaskellTypes where

postulate String : Set
{-# BUILTIN STRING String #-}

data Prod (A : Set) (B : Set) : Set where
  _,_ : A → B → Prod A B
{-# COMPILED_DATA Prod (,) (,) #-}

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
{-# COMPILED_DATA List [] [] (:) #-}
