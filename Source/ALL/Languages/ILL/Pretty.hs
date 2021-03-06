module Languages.ILL.Pretty where

import Data.Text

import Languages.ILL.TypeSyntax
import Languages.ILL.Intermediate

parenType :: (Type -> String) -> Type -> String
parenType f t@(Imp _ _) = "(" ++ f t ++ ")"
parenType f t@(Tensor _ _) = "(" ++ f t ++ ")"
parenType f t = f t

parenITType :: (Type -> String) -> Type -> String
parenITType f t@(Tensor _ _) = "(" ++ f t ++ ")"
parenITType f t = f t

parenTType :: (Type -> String) -> Type -> String
parenTType f t@(Imp _ _) = "(" ++ f t ++ ")"
parenTType f t = f t

parenBType :: (Type -> String) -> Type -> String
parenBType f t@(Imp _ _) = "(" ++ f t ++ ")"
parenBType f t@(Tensor _ _) = "(" ++ f t ++ ")"
parenBType f t = f t
                 
prettyType :: Type -> String
prettyType (TVar x) = unpack x
prettyType Top = "Top"
prettyType (Imp a b) = (parenType prettyType a) ++ " -o " ++ (parenITType prettyType b)
prettyType (Tensor a b) = (parenTType prettyType a) ++ " (x) " ++ (parenTType prettyType b)
prettyType (Bang a) = "!" ++ (parenBType prettyType a)

prettyTerm :: ITerm -> String
prettyTerm = undefined