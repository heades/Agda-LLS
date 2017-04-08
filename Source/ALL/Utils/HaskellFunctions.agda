module Utils.HaskellFunctions where

open import bool
open import maybe

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

fstT : {A B C : Set} → Triple A B C → A
fstT (triple x y z) = x

sndT : {A B C : Set} → Triple A B C → B
sndT (triple x y z) = y

trdT : {A B C : Set} → Triple A B C → C
trdT (triple x y z) = z

fstMapT : {A₁ A₂ B C : Set} → (A₁ → A₂) → Triple A₁ B C → Triple A₂ B C
fstMapT f (triple x y z) = triple (f x) y z

_++_ : {A : Set} → List A → List A → List A
[] ++ l₂ = l₂
(x :: l₁) ++ l₂ = x :: (l₁ ++ l₂)

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

lookup : ∀{A B} → (A → A → 𝔹) → A → List (Prod A B) → maybe B
lookup _eq_ x [] = nothing
lookup _eq_ x ((y , b) :: l) with x eq y
... | tt = just b
... | ff = lookup _eq_ x l
