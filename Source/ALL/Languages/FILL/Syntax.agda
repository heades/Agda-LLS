module Languages.FILL.Syntax where

open import level
open import bool
open import nat
open import unit
open import empty
open import list
open import eq
open import sum

open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Languages.FILL.TypeSyntax

True : Set
True = ⊤{lzero}

False : Set
False = ⊥{lzero}

Name : Set
Name = ℕ

name-in : ∀{A : Set} → (A → A → 𝔹) → A → 𝕃 A → Set
name-in eq x ctx with list-member eq x ctx
name-in _ x ctx | tt = True
name-in _ x ctx | ff = False

-- Bound Variable Labels:
data VLabel : Set where
  LPV : VLabel         -- Let-Bound Left Pattern Variable
  RPV : VLabel         -- Let-Bound Right Pattern Variable
  BV  : VLabel         -- λ-Bound Variable

_vl-eq_ : VLabel → VLabel → 𝔹
LPV vl-eq LPV = tt
RPV vl-eq RPV = tt
BV vl-eq BV = tt
_ vl-eq _ = ff

data Pattern : Set where
  PTriv : Pattern
  PTensor : Pattern
  PPar : Pattern

data Term : Set where
  Triv : Term
  Void : Term
  FVar : String → Term
  BVar : Name → VLabel → Term
  Let : Term → Type → Pattern → Term → Term  
  Lam : Type → Term → Term
  App : Term → Term → Term
  Tensor : Term → Term → Term
  Par : Term → Term → Term

open-t : Name → VLabel → Term → Term → Term
open-t x l u (BVar y l') with x =ℕ y | l vl-eq l'
... | tt | tt = u
... | _  | _  = BVar y l'
open-t x BV u (Let t₁ y z t₂) = Let (open-t x BV u t₁) y z (open-t x BV u t₂)
open-t x l u (Let t₁ y z t₂) = Let (open-t (suc x) l u t₁) y z (open-t (suc x) l u t₂)
open-t x BV u (Lam y t) = Lam y (open-t (suc x) BV u t)
open-t x l u (Lam y t) = Lam y (open-t x l u t)
open-t x l u (App t₁ t₂) = App (open-t x l u t₁) (open-t x l u t₂)
open-t x l u (Tensor t₁ t₂) = Tensor (open-t x l u t₁) (open-t x l u t₂)
open-t x l u (Par t₁ t₂) = Par (open-t x l u t₁) (open-t x l u t₂)
open-t _ _ _ t = t

close-t : Name → VLabel → String → Term → Term
close-t x l y (FVar z) with y str-eq z
... | tt = BVar x l
... | ff = FVar z
close-t x l y (Let t₁ ty p t₂) = Let (close-t x l y t₁) ty p (close-t x l y t₂)
close-t x l y (Lam z t) = Lam z (close-t x l y t)
close-t x l y (App t₁ t₂) = App (close-t x l y t₁) (close-t x l y t₂)
close-t x l y (Tensor t₁ t₂) = Tensor (close-t x l y t₁) (close-t x l y t₂)
close-t x l y (Par t₁ t₂) = Par (close-t x l y t₁) (close-t x l y t₂)
close-t _ _ _ t = t

data LC : Term → Set where
  Triv : LC Triv
  Void : LC Void
  FVar : ∀{x : String} → LC (FVar x)
  Lam : ∀{ns : 𝕃 String}{t : Term}{a : Type}      
      → LC t      
      → (∀{x : String}
           → (name-in _str-eq_ x ns → False)
           → LC (open-t 0 BV (FVar x) t))
      → LC (Lam a t)
  LetTriv : ∀{t₁ : Term}{a : Type}{t₂ : Term}
      → LC t₁
      → LC t₂
      → LC (Let t₁ a PTriv t₂)      
  Let : ∀{ns : 𝕃 String}{t₁ : Term}{a : Type}{p : Pattern}{t₂ : Term}
      → (p ≡ PTensor) ∨ (p ≡ PPar)
      → LC t₁
      → LC t₂
      → (∀{x y : String}
           → (name-in _str-eq_ x ns → False)
           → (name-in _str-eq_ y ns → False)
           → LC (open-t 0 LPV (FVar x) (open-t 0 RPV (FVar y) t₂)))
      → LC (Let t₁ a p t₂)
  App : ∀{t₁ t₂ : Term}
      → LC t₁
      → LC t₂
      → LC (App t₁ t₂)
  Tensor : ∀{t₁ t₂ : Term}
      → LC t₁
      → LC t₂
      → LC (Tensor t₁ t₂)
  Par : ∀{t₁ t₂ : Term}
      → LC t₁
      → LC t₂
      → LC (Par t₁ t₂)
