module UAE1 where

data Term = V Val
    | NV NumVal
    | Pred Term
    | Succ Term
    | IsZero Term
    | IfThenElse Term Term Term
    deriving (Show, Eq)

data Val = T        -- True
    | F             -- False
    deriving (Show, Eq)

data NumVal = Z | SuccVal NumVal    -- Z is Zero
    deriving (Show, Eq)