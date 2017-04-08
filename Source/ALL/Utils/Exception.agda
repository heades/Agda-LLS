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

commExpTriple : {X A B C : Set} → Triple (Either X A) B C → Either X (Triple A B C)
commExpTriple (triple (Left e) b c) = error e
commExpTriple (triple (Right a) b c) = right (triple a b c)

commExpList : {X A : Set} → List (Either X A) → Either X (List A)
commExpList [] = right []
commExpList (Left e :: xs) = Left e
commExpList (Right y :: xs) = (commExpList xs) >>=E (λ ys → right (y :: ys))

data Exception : Set where
  IllformedLetPattern : Exception
  IllformedPromote : Exception
  VarNotInCtx : Exception
  Nonlinearity : Exception
  NonlocallyClosed : Exception
  NonEmptyCtx : Exception
  TypeErrorLetNotTop : Exception
  TypeErrorLetNotTensor : Exception
  TypeErrorPromoteNotBang : Exception
  TypeErrorTypesNotEqual : Exception
  TypeErrorAppNotImp : Exception
{-# COMPILED_DATA Exception Utils.Exception.Exception Utils.Exception.IllformedLetPattern 
                                                      Utils.Exception.IllformedPromote
                                                      Utils.Exception.VarNotInCtx 
                                                      Utils.Exception.Nonlinearity
                                                      Utils.Exception.NonlocallyClosed 
                                                      Utils.Exception.NonEmptyCtx
                                                      Utils.Exception.TypeErrorLetNotTop 
                                                      Utils.Exception.TypeErrorLetNotTensor
                                                      Utils.Exception.TypeErrorPromoteNotBang 
                                                      Utils.Exception.TypeErrorTypesNotEqual 
                                                      Utils.Exception.TypeErrorAppNotImp #-}
