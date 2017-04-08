module Utils.HaskellTypes where

postulate String : Set
{-# BUILTIN STRING String #-}

data Unit : Set where
  triv : Unit
{-# COMPILED_DATA Unit () () #-}

data Prod (A : Set) (B : Set) : Set where
  _,_ : A → B → Prod A B
{-# COMPILED_DATA Prod (,) (,) #-}

data Triple (A B C : Set) : Set where
  triple : A → B → C → Triple A B C
{-# COMPILED_DATA Triple (,,) (,,) #-}

infixr 20 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
{-# COMPILED_DATA List [] [] (:) #-}
