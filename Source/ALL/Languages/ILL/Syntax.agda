module Languages.ILL.Syntax where

open import level
open import bool
open import nat
open import unit
open import empty
open import eq
open import sum
open import product

open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Languages.ILL.TypeSyntax

True : Set
True = ⊤{lzero}

False : Set
False = ⊥{lzero}

Name : Set
Name = ℕ

name-in : ∀{A : Set} → (A → A → 𝔹) → A → List A → Set
name-in eq x ctx with list-member eq x ctx
name-in _ x ctx | tt = True
name-in _ x ctx | ff = False

-- Bound Variable Labels:
data VLabel : Set where
  LLPV : VLabel         -- Let-Bound Left Pattern Variable
  RLPV : VLabel         -- Let-Bound Right Pattern Variable
  LCPV : VLabel         -- Copy-Bound Left Pattern Variable
  RCPV : VLabel         -- Copy-Bound Right Pattern Variable  
  BV  : VLabel          -- λ-Bound Variable
  PBV : VLabel      -- Promote-Bound Variable that is ith in the sequence
  
_vl-eq_ : VLabel → VLabel → 𝔹
LLPV vl-eq LLPV = tt
RLPV vl-eq RLPV = tt
LCPV vl-eq LCPV = tt
RCPV vl-eq RCPV = tt
BV vl-eq BV = tt
PBV vl-eq PBV = tt
_ vl-eq _ = ff

data Pattern : Set where
  PTriv : Pattern
  PTensor : String → String → Pattern

data Term : Set where
  Triv : Term
  FVar : String → Term
  BVar : Name → String → VLabel → Term
  Let : Term → Type → Pattern → Term → Term  
  Lam : String → Type → Term → Term
  App : Term → Term → Term
  Tensor : Term → Term → Term
  Promote : List Term → List (Prod String Type) → Term → Term
  Discard : Term → Term → Term
  Copy : Term → (Prod String String) → Term → Term
  Derelict : Term → Term  

{-# TERMINATING #-}
open-t : Name → VLabel → Term → Term → Term
open-t x l u (BVar y ys l') with x =ℕ y | l vl-eq l'
... | tt | tt = u
... | _  | _  = BVar y ys l'
open-t x BV u (Let t₁ y z t₂) = Let (open-t x BV u t₁) y z (open-t x BV u t₂)
open-t x l@LCPV u (Let t₁ y z t₂) = Let (open-t x l u t₁) y z (open-t x l u t₂)
open-t x l@RCPV u (Let t₁ y z t₂) = Let (open-t x l u t₁) y z (open-t x l u t₂)
open-t x l u (Let t₁ a p t₂) = Let (open-t x l u t₁) a p (open-t (suc x) l u t₂)
open-t x BV u (Lam ys a t) = Lam ys a (open-t (suc x) BV u t)
open-t x l u (Lam ys a t) = Lam ys a (open-t x l u t)
open-t x l u (App t₁ t₂) = App (open-t x l u t₁) (open-t x l u t₂)
open-t x l u (Tensor t₁ t₂) = Tensor (open-t x l u t₁) (open-t x l u t₂)
open-t x l@PBV y (Promote ms xs n) = Promote oms xs (open-t (suc x) l y n)
  where
    oms = map (open-t x l y) ms
open-t x l y (Promote ms xs n) = Promote oms xs (open-t x l y n)
  where
    oms = map (open-t x l y) ms
open-t x l@LCPV y (Copy m p n) = Copy (open-t x l y m ) p (open-t (suc x) l y n)
open-t x l@RCPV y (Copy m p n) = Copy (open-t x l y m ) p (open-t (suc x) l y n)
open-t x l y (Copy m p n) = Copy (open-t x l y m ) p (open-t x l y n)
open-t x l y (Discard m n) = Discard (open-t x l y m) (open-t x l y n)
open-t x l y (Derelict m) = Derelict (open-t x l y m)
open-t _ _ _ t = t

{-# TERMINATING #-}
close-t : Name → String → VLabel → String → Term → Term
close-t x xs l y (FVar z) with y str-eq z
... | tt = BVar x xs l
... | ff = FVar z
close-t x xs l@LLPV y (Let t₁ ty p t₂) = Let (close-t x xs l y t₁) ty p (close-t (suc x) xs l y t₂)
close-t x xs l@RLPV y (Let t₁ ty p t₂) = Let (close-t x xs l y t₁) ty p (close-t (suc x) xs l y t₂)
close-t x xs l y (Let t₁ ty p t₂) = Let (close-t x xs l y t₁) ty p (close-t x xs l y t₂)
close-t x xs l@BV y (Lam ys a t) = Lam ys a (close-t (suc x) xs l y t)
close-t x xs l y (Lam ys a t) = Lam ys a (close-t x xs l y t)
close-t x xs l y (App t₁ t₂) = App (close-t x xs l y t₁) (close-t x xs l y t₂)
close-t x xs l y (Tensor t₁ t₂) = Tensor (close-t x xs l y t₁) (close-t x xs l y t₂)
close-t x xs l@PBV y (Promote ms zs n) = Promote cms zs (close-t (suc x) xs l y n)
  where
    cms = map (close-t x xs l y) ms
close-t x xs l y (Promote ms zs n) = Promote cms zs (close-t x xs l y n)
  where
    cms = map (close-t x xs l y) ms    
close-t x xs l@LCPV y (Copy m p n) = Copy (close-t x xs l y m) p (close-t (suc x) xs l y n)
close-t x xs l@RCPV y (Copy m p n) = Copy (close-t x xs l y m) p (close-t (suc x) xs l y n)
close-t x xs l y (Copy m p n) = Copy (close-t x xs l y m) p (close-t x xs l y n)
close-t x xs l y (Discard m n) = Discard (close-t x xs l y m) (close-t x xs l y n)
close-t x xs l y (Derelict m) = Derelict (close-t x xs l y m)
close-t _ _ _ _ t = t
