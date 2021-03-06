module Utils.Exception where

data Exception = IllformedLetPattern
               | VarNotInCtx
               | Nonlinearity
               | NonlocallyClosed
               | NonEmptyCtx
               | TypeErrorLetNotTop
               | TypeErrorLetNotTensor
               | IllformedPromote
               | TypeErrorPromoteNotBang
               | TypeErrorTypesNotEqual
               | TypeErrorAppNotImp
               | NonLinearCtx
               | TypeErrorDuplicatedFreeVar
 deriving Show