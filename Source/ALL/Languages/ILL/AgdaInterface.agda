module Languages.ILL.AgdaInterface where

open import nat

open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Utils.Exception
open import Languages.ILL.Intermediate
open import Languages.ILL.Syntax
open import Languages.ILL.TypeSyntax

{-# TERMINATING #-}
translate : ITerm → Either Exception Term
translate = translate' 0 0 0 0
 where
   -- n : the next fresh λ-bound variable name
   -- m : the next fresh let-bound pattern variable name
   -- c : the next fresh copy-bound variable name
   -- p : the next fresh promote-bound variable name
   translate' : Name → Name → Name → Name → ITerm → Either Exception Term
   translate' n m c p Triv = right Triv
   translate' n m c p (Var x) = right (FVar x)
   translate' n m c p (TTensor t₁ t₂) =
     (translate' n m c p t₁)
       >>=E (λ e₁ → (translate' n m c p t₂)
         >>=E (λ e₂ → right (Tensor e₁ e₂)))
   translate' n m c p (Lam x a t) =
     (translate' (suc n) m c p t)
       >>=E (λ e → right (Lam x a (close-t n x BV x e)))
   translate' n m c p (Let t₁ a PTriv t₂) =
     (translate' n m c p t₁)
       >>=E (λ e₁ → (translate' n m c p t₂)
         >>=E (λ e₂ → right (Let e₁ a PTriv e₂)))
   translate' n m c p (Let t₁ a (PTensor (PVar x) (PVar y)) t₂) =
     (translate' n m c p t₁)
       >>=E (λ e₁ → (translate' n (suc m) c p t₂)
         >>=E (λ e₂ → right (Let e₁ a (PTensor x y) (close-t m x LLPV x (close-t m y RLPV y e₂)))))
   translate' n m c p (Let _ _ _ _) = error IllformedLetPattern 
   translate' n m c p (App t₁ t₂) =
     (translate' n m c p t₁)
       >>=E (λ e₁ → (translate' n m c p t₂)
         >>=E (λ e₂ → right (App e₁ e₂)))
   translate' n m c p (Promote ts t) =
      tts >>=E
      (λ ttts → (translate' n m c (suc p) t) >>=E
        (λ tt → right (Promote ttts (foldr aux tt ts)) )) 
    where
      tts = commExpList (map (λ x → commExpTriple (fstMapT (translate' n m c p) x)) ts)
      aux = (λ (x : Triple ITerm String Type) (v : Term) → close-t p (sndT x) PBV (sndT x) v)
   translate' n m c p (Copy t₁ x y t₂) =
     (translate' n m c p t₁) >>=E
       (λ tt₁ → (translate' n m (suc c) p t₂) >>=E
         (λ tt₂ → Right (close-t c x LCPV x (close-t c y RCPV y tt₂))))
   translate' n m c p (Discard t₁ t₂) =
     (translate' n m c p t₁) >>=E
       (λ tt₁ → translate' n m c p t₂ >>=E
         (λ tt₂ → right (Discard tt₁ tt₂)))
   translate' n m c p (Derelict t) =
     (translate' n m c p t) >>=E (λ tt → right (Derelict tt))

{-# TERMINATING #-}
untranslate : Term → ITerm
untranslate Triv = Triv
untranslate (FVar x) = Var x
untranslate (BVar _ x _) = Var x
untranslate (Let t₁ a PTriv t₂) = Let (untranslate t₁) a PTriv (untranslate t₂)
untranslate (Let t₁ a (PTensor xs ys) t₂) = Let (untranslate t₁) a (PTensor (PVar xs) (PVar ys)) (untranslate t₂)
untranslate (Lam x a t) = Lam x a (untranslate t)
untranslate (App t₁ t₂) = App (untranslate t₁) (untranslate t₂)
untranslate (Tensor t₁ t₂) = TTensor (untranslate t₁) (untranslate t₂)
untranslate (Promote ts t) = Promote uts (untranslate t)
  where
   uts = map (fstMapT untranslate) ts
untranslate (Copy t₁ p t₂) = Copy (untranslate t₁) (fst p) (snd p) (untranslate t₂)
untranslate (Discard t₁ t₂) = Discard (untranslate t₁) (untranslate t₂)
untranslate (Derelict t) = Derelict (untranslate t)

transUntransId : ITerm → Either Exception ITerm
transUntransId t = (translate t) >>=E (λ e → right (untranslate e))
{-# COMPILED_EXPORT transUntransId transUntransId #-}
