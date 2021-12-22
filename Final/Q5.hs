{-# LANGUAGE EmptyDataDecls, EmptyDataDeriving #-}
module Q5 where

data T = App T T
    | Val V
    | Raise T
    | TryWith T T
    deriving (Show, Eq)

data V deriving (Show, Eq)

-- Encodes the small-step semantics for error handling
ssos :: T -> T
ssos (App (Val _) (Raise v2@(Val _))) = Raise v2        -- E-AppRaise2
ssos (App (Raise v1@(Val _)) _) = Raise v1              -- E-AppRaise1
ssos (Raise (Raise v1@(Val _))) = Raise v1              -- E-RaiseRaise
ssos (Raise t) = Raise (ssos t)                         -- E-Raise
ssos (TryWith v1@(Val _) _) = v1                        -- E-TryV
ssos (TryWith (Raise v1@(Val _)) t2) = App t2 v1        -- E-TryRaise
ssos (TryWith t1 t2) = TryWith (ssos t1) t2             -- E-Try
ssos t = t          -- Reflexivity