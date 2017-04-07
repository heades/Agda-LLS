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
  PTensor : String → String → Pattern
  PPar : String → String → Pattern

data Term : Set where
  Triv : Term
  Void : Term
  FVar : String → Term
  BVar : Name → String → VLabel → Term
  Let : Term → Type → Pattern → Term → Term  
  Lam : String → Type → Term → Term
  App : Term → Term → Term
  Tensor : Term → Term → Term
  Par : Term → Term → Term

open-t : Name → VLabel → Term → Term → Term
open-t x l u (BVar y ys l') with x =ℕ y | l vl-eq l'
... | tt | tt = u
... | _  | _  = BVar y ys l'
open-t x BV u (Let t₁ y z t₂) = Let (open-t x BV u t₁) y z (open-t x BV u t₂)
open-t x l u (Let t₁ a p t₂) = Let (open-t (suc x) l u t₁) a p (open-t (suc x) l u t₂)
open-t x BV u (Lam ys a t) = Lam ys a (open-t (suc x) BV u t)
open-t x l u (Lam ys a t) = Lam ys a (open-t x l u t)
open-t x l u (App t₁ t₂) = App (open-t x l u t₁) (open-t x l u t₂)
open-t x l u (Tensor t₁ t₂) = Tensor (open-t x l u t₁) (open-t x l u t₂)
open-t x l u (Par t₁ t₂) = Par (open-t x l u t₁) (open-t x l u t₂)
open-t _ _ _ t = t

close-t : Name → String → VLabel → String → Term → Term
close-t x xs l y (FVar z) with y str-eq z
... | tt = BVar x xs l
... | ff = FVar z
close-t x xs l y (Let t₁ ty p t₂) = Let (close-t x xs l y t₁) ty p (close-t x xs l y t₂)
close-t x xs l y (Lam ys a t) = Lam ys a (close-t x xs l y t)
close-t x xs l y (App t₁ t₂) = App (close-t x xs l y t₁) (close-t x xs l y t₂)
close-t x xs l y (Tensor t₁ t₂) = Tensor (close-t x xs l y t₁) (close-t x xs l y t₂)
close-t x xs l y (Par t₁ t₂) = Par (close-t x xs l y t₁) (close-t x xs l y t₂)
close-t _ _ _ _ t = t

data LC : Term → Set where
  Triv : LC Triv
  Void : LC Void
  FVar : ∀{x : String} → LC (FVar x)
  Lam : ∀{ns : 𝕃 String}{t : Term}{a : Type}{y : String}
      → LC t      
      → (∀{x : String}
           → (name-in _str-eq_ x ns → False)
           → LC (open-t 0 BV (FVar x) t))
      → LC (Lam y a t)
  LetTriv : ∀{t₁ : Term}{a : Type}{t₂ : Term}
      → LC t₁
      → LC t₂
      → LC (Let t₁ a PTriv t₂)      
  LetTensor : ∀{ns : 𝕃 String}{t₁ : Term}{a : Type}{t₂ : Term}{s₁ s₂ : String}
      → LC t₁
      → LC t₂
      → (∀{x y : String}
           → (name-in _str-eq_ x ns → False)
           → (name-in _str-eq_ y ns → False)
           → LC (open-t 0 LPV (FVar x) (open-t 0 RPV (FVar y) t₂)))
      → LC (Let t₁ a (PTensor s₁ s₂) t₂)
  LetPar : ∀{ns : 𝕃 String}{t₁ : Term}{a : Type}{t₂ : Term}{s₁ s₂ : String}
      → LC t₁
      → LC t₂
      → (∀{x y : String}
           → (name-in _str-eq_ x ns → False)
           → (name-in _str-eq_ y ns → False)
           → LC (open-t 0 LPV (FVar x) (open-t 0 RPV (FVar y) t₂)))
      → LC (Let t₁ a (PPar s₁ s₂) t₂)      
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
