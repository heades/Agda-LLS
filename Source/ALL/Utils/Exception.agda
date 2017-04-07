module Utils.Exception where

{-# IMPORT Utils.Exception #-}

open import Utils.HaskellTypes


data Either (A : Set) (B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILED_DATA Either Either Left Right #-}

right : ∀{X A : Set} → A → Either X A
right x = Right x

error : ∀{X A : Set} → X → Either X A
error e = Left e

_>>=E_ : ∀{X A B : Set} → Either X A → (A → Either X B) → Either X B
_>>=E_ (Left x) f = Left x
_>>=E_ (Right x) f = f x

commExpList : {X A : Set} → List (Either X A) → Either X (List A)
commExpList [] = right []
commExpList (Left e :: xs) = Left e
commExpList (Right y :: xs) = (commExpList xs) >>=E (λ ys → right (y :: ys))

data Exception : Set where
  IllformedLetPattern : Exception
{-# COMPILED_DATA Exception Utils.Exception.Exception Utils.Exception.IllformedLetPattern #-}
