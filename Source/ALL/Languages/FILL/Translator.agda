module Languages.FILL.Translator where

open import nat

open import Utils.HaskellTypes
open import Utils.Exception
open import Languages.FILL.Intermediate
open import Languages.FILL.Syntax

translate : ITerm → Either Exception Term
translate = translate' 0 0
 where
   -- n : the next fresh bound variable name
   -- m : the next fresh bound pattern variable name
   translate' : Name → Name → ITerm → Either Exception Term
   translate' n m Triv = right Triv
   translate' n m Void = right Void
   translate' n m (Var x) = right (FVar x)
   translate' n m (TTensor t₁ t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (Tensor e₁ e₂)))
   translate' n m (TPar t₁ t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (Par e₁ e₂)))
   translate' n m (Lam x a t) =
     (translate' (suc n) m t)
       >>=E (λ e → right (Lam a (close-t n BV x e)))
   translate' n m (Let t₁ a PTriv t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (Let e₁ a PTriv e₂)))
   translate' n m (Let t₁ a (PTensor (PVar x) (PVar y)) t₂) =
     (translate' n (suc m) t₁)
       >>=E (λ e₁ → (translate' n (suc m) t₂)
         >>=E (λ e₂ → right (Let e₁ a PTensor (close-t m LPV x (close-t m RPV y e₂)))))
   translate' n m (Let t₁ a (PPar (PVar x) (PVar y)) t₂) =
     (translate' n (suc m) t₁)
       >>=E (λ e₁ → (translate' n (suc m) t₂)
         >>=E (λ e₂ → right (Let e₁ a PPar (close-t m LPV x (close-t m RPV y e₂)))))
   translate' n m (Let _ _ _ _) = error IllformedLetPattern 
   translate' n m (App t₁ t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (App e₁ e₂)))
