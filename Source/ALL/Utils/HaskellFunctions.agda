module Utils.HaskellFunctions where

open import bool

open import Utils.HaskellTypes

postulate _str-eq_ : String → String → 𝔹
{-# COMPILED _str-eq_ (==) #-}

infixr 20 _++s_
postulate _++s_ : String → String → String
{-# COMPILED _++s_ Data.Text.append #-}

fst : {A B : Set} → Prod A B → A
fst (x , y) = x

snd : {A B : Set} → Prod A B → B
snd (x , y) = y

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

list-member : {A : Set}(eq : A → A → 𝔹)(a : A)(l : List A) → 𝔹
list-member eq a [] = ff
list-member eq a (x :: xs) with eq a x
... | tt = tt
... | ff = list-member eq a xs

foldr : {A : Set}{B : Set} → (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (a :: as) = f a (foldr f b as)

