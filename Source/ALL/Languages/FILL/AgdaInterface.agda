module Languages.FILL.AgdaInterface where

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
       >>=E (λ e → right (Lam x a (close-t n x BV x e)))
   translate' n m (Let t₁ a PTriv t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (Let e₁ a PTriv e₂)))
   translate' n m (Let t₁ a (PTensor (PVar x) (PVar y)) t₂) =
     (translate' n (suc m) t₁)
       >>=E (λ e₁ → (translate' n (suc m) t₂)
         >>=E (λ e₂ → right (Let e₁ a (PTensor x y) (close-t m x LPV x (close-t m y RPV y e₂)))))
   translate' n m (Let t₁ a (PPar (PVar x) (PVar y)) t₂) =
     (translate' n (suc m) t₁)
       >>=E (λ e₁ → (translate' n (suc m) t₂)
         >>=E (λ e₂ → right (Let e₁ a (PPar x y) (close-t m x LPV x (close-t m y RPV y e₂)))))
   translate' n m (Let _ _ _ _) = error IllformedLetPattern 
   translate' n m (App t₁ t₂) =
     (translate' n m t₁)
       >>=E (λ e₁ → (translate' n m t₂)
         >>=E (λ e₂ → right (App e₁ e₂)))

untranslate : Term → ITerm
untranslate Triv = Triv
untranslate Void = Void
untranslate (FVar x) = Var x
untranslate (BVar _ x _) = Var x
untranslate (Let t₁ a PTriv t₂) = Let (untranslate t₁) a PTriv (untranslate t₂)
untranslate (Let t₁ a (PTensor xs ys) t₂) = Let (untranslate t₁) a (PTensor (PVar xs) (PVar ys)) (untranslate t₂)
untranslate (Let t₁ a (PPar xs ys) t₂) = Let (untranslate t₁) a (PPar (PVar xs) (PVar ys)) (untranslate t₂)
untranslate (Lam x a t) = Lam x a (untranslate t)
untranslate (App t₁ t₂) = App (untranslate t₁) (untranslate t₂)
untranslate (Tensor t₁ t₂) = TTensor (untranslate t₁) (untranslate t₂)
untranslate (Par t₁ t₂) = TPar (untranslate t₁) (untranslate t₂)

transUntransId : ITerm → Either Exception ITerm
transUntransId t = (translate t) >>=E (λ e → right (untranslate e))

{-# COMPILED_EXPORT transUntransId transUntransId #-}
