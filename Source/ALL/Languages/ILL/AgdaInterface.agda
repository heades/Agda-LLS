module Languages.ILL.AgdaInterface where

open import nat

open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Utils.Exception
open import Languages.ILL.Intermediate
open import Languages.ILL.Syntax
open import Languages.ILL.TypeSyntax
open import Languages.ILL.TypeCheck

{-# TERMINATING #-}
translate : ITerm → Either Exception Term
translate Triv = right Triv
translate (Var x) = right (FVar x)
translate (TTensor t₁ t₂) =
   (translate t₁)
     >>=E (λ e₁ → (translate t₂)
       >>=E (λ e₂ → right (Tensor e₁ e₂)))
translate (Lam x a t) =
  (translate t)
    >>=E (λ e → right (Lam x a (close-t 0 x BV x e)))
translate (Let t₁ a PTriv t₂) =
  (translate t₁)
    >>=E (λ e₁ → (translate t₂)
      >>=E (λ e₂ → right (Let e₁ a PTriv e₂)))
translate (Let t₁ a (PTensor (PVar x) (PVar y)) t₂) =
  (translate t₁)
    >>=E (λ e₁ → (translate t₂)
      >>=E (λ e₂ → right (Let e₁ a (PTensor x y) (close-t 0 x LLPV x (close-t 0 y RLPV y e₂)))))
translate (Let _ _ _ _) = error IllformedLetPattern 
translate (App t₁ t₂) =
  (translate t₁)
    >>=E (λ e₁ → (translate t₂)
      >>=E (λ e₂ → right (App e₁ e₂)))
translate (Promote ts t) =
   tts >>=E
   (λ ttts → (translate t) >>=E
     (λ tt → right (Promote ttts (foldr aux tt ts)) )) 
 where
   tts = commExpList (map (λ x → commExpTriple (fstMapT translate x)) ts)
   aux = (λ (x : Triple ITerm String Type) (v : Term) → close-t 0 (sndT x) PBV (sndT x) v)
translate (Copy t₁ x y t₂) =
  (translate t₁) >>=E
    (λ tt₁ → (translate t₂) >>=E
      (λ tt₂ → Right (close-t 0 x LCPV x (close-t 0 y RCPV y tt₂))))
translate (Discard t₁ t₂) =
  (translate t₁) >>=E
    (λ tt₁ → translate t₂ >>=E
      (λ tt₂ → right (Discard tt₁ tt₂)))
translate (Derelict t) =
  (translate t) >>=E (λ tt → right (Derelict tt))

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

runTypeCheck : ITerm → Either Exception Type
runTypeCheck it = (translate it) >>=E (λ t → typeCheck t)
{-# COMPILED_EXPORT runTypeCheck runTypeCheck #-}
