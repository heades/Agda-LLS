module Languages.ILL.TypeCheck where

open import bool
open import maybe

open import Languages.ILL.TypeSyntax
open import Languages.ILL.Syntax
open import Utils.HaskellTypes
open import Utils.HaskellFunctions
open import Utils.Exception

data StateT (s : Set) (m : Set → Set) (a : Set) : Set where
  stateT : (s → m (Prod a s)) → StateT s m a

runStateT : ∀{s m a} → StateT s m a → (s → m (Prod a s))
runStateT (stateT f) = f

returnSTE : ∀{s A} → A → StateT s (Either Exception) A
returnSTE x = stateT (λ y → right (x , y))

infixl 20 _>>=STE_
_>>=STE_ : ∀{s A B} → StateT s (Either Exception) A → (A → StateT s (Either Exception) B) → StateT s (Either Exception) B
(stateT st) >>=STE f = stateT (λ y → st y >>=E (λ p → runStateT (f (fst p)) (snd p)))

infixl 20 _>>STE_
_>>STE_ : ∀{s A B} → StateT s (Either Exception) A → StateT s (Either Exception) B → StateT s (Either Exception) B
c₁ >>STE c₂ = c₁ >>=STE (λ _ → c₂)

throw : ∀{s A} → Exception → StateT s (Either Exception) A
throw x = stateT (λ _ → error x)

lift : ∀{s A} → Either Exception A → StateT s (Either Exception) A
lift (Left x) = stateT (λ _ → error x)
lift (Right x) = stateT (λ y → right (x , y))

get : ∀{S} → StateT S (Either Exception) S
get = stateT (λ x → right (x , x))

put : ∀{S} → S → StateT S (Either Exception) Unit
put s = stateT (λ x → Right (triv , s))

CTX : Set
CTX = List (Prod String Type)

TC : Set → Set
TC = StateT CTX (Either Exception)

getTypeCTX : String → CTX → maybe Type
getTypeCTX x ctx = lookup _str-eq_ x ctx

{-# TERMINATING #-}
subctxFV : CTX → Term → Either Exception CTX
subctxFV ctx Triv = right []
subctxFV ctx t@(FVar x) with getTypeCTX x ctx
... | just ty = right ((x , ty) :: [])
... | nothing = error VarNotInCtx
subctxFV ctx (BVar _ _ _) = right []
subctxFV ctx (Let t₁ _ _ t₂) =
  (subctxFV ctx t₁) >>=E
    (λ l₁ → (subctxFV ctx t₂) >>=E
       λ l₂ → right (l₁ ++ l₂))
subctxFV ctx (Lam _ _ t) = subctxFV ctx t
subctxFV ctx (App t₁ t₂) =
  (subctxFV ctx t₁) >>=E
    (λ l₁ → (subctxFV ctx t₂) >>=E
       λ l₂ → right (l₁ ++ l₂))
subctxFV ctx (Tensor t₁ t₂) =
  (subctxFV ctx t₁) >>=E
    (λ l₁ → (subctxFV ctx t₂) >>=E
       λ l₂ → right (l₁ ++ l₂))
subctxFV ctx (Promote ms t) =
  mctx₁ >>=E
    (λ ctx₁ → (subctxFV ctx t) >>=E
      (λ ctx₂ → right (ctx₁ ++ ctx₂)))
 where
  aux = (λ m r →
    (subctxFV ctx (fstT m)) >>=E
      (λ l₁ → r >>=E
        (λ l₂ → right (l₁ ++ l₂))))
  mctx₁ = foldr aux (right []) ms
subctxFV ctx (Discard t₁ t₂) =
  (subctxFV ctx t₁) >>=E
    (λ l₁ → (subctxFV ctx t₂) >>=E
       λ l₂ → right (l₁ ++ l₂))
subctxFV ctx (Copy t₁ _ t₂) =
  (subctxFV ctx t₁) >>=E
    (λ l₁ → (subctxFV ctx t₂) >>=E
       λ l₂ → right (l₁ ++ l₂))
subctxFV ctx (Derelict t) = subctxFV ctx t

isTop : Type → TC Type
isTop Top = returnSTE Top
isTop _ = throw TypeErrorLetNotTop
  
isTensor : Type → TC (Prod Type Type)
isTensor (Tensor x y) = returnSTE (x , y)
isTensor _ = throw TypeErrorLetNotTensor

isBang : Type → TC Type
isBang (Bang ty) = returnSTE ty
isBang _ = throw TypeErrorPromoteNotBang

isImp : Type → TC (Prod Type Type)
isImp (Imp A B) = returnSTE (A , B)
isImp _ = throw TypeErrorAppNotImp

_tyEq_ : Type → Type → TC Unit
_tyEq_ ty₁ ty₂ with ty₁ eq-type ty₂
... | tt = returnSTE triv
... | ff = throw TypeErrorTypesNotEqual

{-# TERMINATING #-}
typeCheck' : Term → TC Type
typeCheck' Triv = get >>=STE checkCTX
 where
   checkCTX : CTX → TC Type
   checkCTX [] = returnSTE Top
   checkCTX _ = throw NonEmptyCtx
typeCheck' (FVar x) = get >>=STE checkCtx
 where
   checkCtx : CTX → TC Type
   checkCtx ((y , ty) :: []) with x str-eq y
   ... | tt = returnSTE ty
   ... | ff = throw VarNotInCtx
   checkCtx _ = throw NonLinearCtx
typeCheck' (BVar _ _ _) = throw NonlocallyClosed
typeCheck' (Let t₁ ty PTriv t₂) = 
 get >>=STE
   (λ ctx → lift (subctxFV ctx t₁) >>=STE
     (λ ctx₁ → lift (subctxFV ctx t₂) >>=STE
       λ ctx₂ → ((put ctx₁) >>STE typeCheck' t₁) >>=STE
         (λ ty₁ → isTop ty₁ >>STE (put ctx₂ >>STE typeCheck' t₂))))
typeCheck' (Let t₁ ty (PTensor x y) t₂) =
  get >>=STE
    (λ ctx → lift (subctxFV ctx t₁) >>=STE
     (λ ctx₁ → lift (subctxFV ctx t₂) >>=STE
      (λ ctx₂ → ((put ctx₁) >>STE typeCheck' t₁) >>=STE
       (λ ty₁ → (isTensor ty₁) >>=STE
        (λ tys → let A = fst tys
                     B = snd tys
                     t₂' = open-t 0 y RLPV (FVar y) (open-t 0 x LLPV (FVar x) t₂)
                  in put ((x , A) :: (y , B) :: ctx₂) >>STE typeCheck' t₂')))))       
typeCheck' (Lam x ty t) =
  get >>=STE
    (λ ctx → (put ((x , ty) :: ctx)) >>STE
      typeCheck' (open-t 0 x BV (FVar x) t) >>=STE
        (λ ty₂ → returnSTE (Imp ty ty₂)))
typeCheck' (App t₁ t₂) =
  get >>=STE
    (λ ctx → lift (subctxFV ctx t₁) >>=STE
      (λ ctx₁ → (put ctx₁) >>STE (typeCheck' t₁) >>=STE
        (λ ty₁ → isImp ty₁ >>=STE
          (λ tys → lift (subctxFV ctx t₂) >>=STE
            (λ ctx₂ → (put ctx₂) >>STE (typeCheck' t₂) >>=STE
              (λ ty₂ → ((fst tys) tyEq ty₂) >>STE returnSTE (snd tys)))))))
typeCheck' (Tensor t₁ t₂) =
  get >>=STE
    (λ ctx → lift (subctxFV ctx t₁) >>=STE
      (λ ctx₁ → (put ctx₁) >>STE typeCheck' t₁) >>=STE
        (λ ty₁ → lift (subctxFV ctx t₂) >>=STE
          (λ ctx₂ → (put ctx₂) >>STE typeCheck' t₂) >>=STE
            (λ ty₂ → returnSTE (Tensor ty₁ ty₂))))
typeCheck' (Promote ms t) =
  put [] >>STE checkVectorOpenTerm ms t
         >>=STE typeCheck'
         >>=STE (λ ty → returnSTE (Bang ty))
 where
   checkVectorTerm : Term → TC Type
   checkVectorTerm t =
     get >>=STE
       (λ ctx → lift (subctxFV ctx t) >>=STE
         (λ ctx₁ → (put ctx₁) >>STE
           typeCheck' t))
           
   checkVectorOpenTerm : List (Triple Term String Type) → Term → TC Term
   checkVectorOpenTerm [] t = throw IllformedPromote
   checkVectorOpenTerm (triple t₁ x₁ ty₁ :: rest) t =
     get >>=STE
       (λ ctx → checkVectorTerm t₁ >>=STE
         (λ ty₁' → (isBang ty₁' >>STE (ty₁ tyEq ty₁')) >>STE
           (put ((x₁ , ty₁) :: ctx) >>STE
             ((checkVectorOpenTerm rest t) >>=STE
               (λ t' → returnSTE (open-t 0 x₁ PBV (FVar x₁) t'))))))
typeCheck' (Discard t₁ t₂) = get >>=STE
   (λ ctx → lift (subctxFV ctx t₁) >>=STE
     (λ ctx₁ → lift (subctxFV ctx t₂) >>=STE
       (λ ctx₂ → (put ctx₁) >>STE typeCheck' t₁
                            >>=STE isBang
                            >>STE (put ctx₂)
                            >>STE typeCheck' t₂)))
typeCheck' (Copy t₁ (x , y) t₂) =
  get >>=STE
       (λ ctx → lift (subctxFV ctx t₁) >>=STE
         (λ ctx₁ → (put ctx₁) >>STE typeCheck' t₁ >>=STE
           (λ ty₁ → isBang ty₁ >>STE lift (subctxFV ctx t₂) >>=STE
             (λ ctx₂ → (put ((x , ty₁) :: (y , ty₁) :: ctx₂) >>STE typeCheck' t₂')))))
 where
   t₂' = open-t 0 y RCPV (FVar y) (open-t 0 x LCPV (FVar x) t₂)
typeCheck' (Derelict t) = typeCheck' t >>=STE isBang 

typeCheck : Term → Either Exception Type
typeCheck t with runStateT (typeCheck' t) []
... | Left e = Left e
... | Right (ty , _) = right ty
