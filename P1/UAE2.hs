module UAE2 where

data Term = V Val
    | NV NumVal
    | Pred Term
    | Succ Term
    | IsZero Term
    | IfThenElse Term Term Term
    deriving (Show, Eq)

data Val = T        -- True
    | F             -- False
    | Wrong         -- Error
    deriving (Show, Eq)

data NumVal = Z | SuccVal NumVal    -- Z is Zero
    deriving (Show, Eq)

-- Small step semantics
ssos :: Term -> Term
ssos (V x) = V x
ssos (NV x) = NV x
ssos (Pred (NV Z)) = NV Z               -- E-PredZero
ssos (Pred (NV (SuccVal x))) = NV x     -- E-PredSucc
ssos (Pred (V _)) = V Wrong             -- E-Pred-Wrong
ssos (Pred t) = Pred $ ssos t           -- E-Pred
ssos (Succ (NV x)) = NV (SuccVal x)     -- Conversion of term succ to nv
ssos (Succ (V _)) = V Wrong             -- E-Succ-Wrong
ssos (Succ t) = Succ $ ssos t           -- E-Succ
ssos (IsZero (NV Z)) = V T              -- E-IsZeroZero
ssos (IsZero (NV (SuccVal _))) = V F    -- E-IsZeroSucc
ssos (IsZero (V _)) = V Wrong           -- E-IsZero-Wrong
ssos (IsZero t) = IsZero $ ssos t       -- E-IsZero
ssos (IfThenElse (NV _) _ _) = V Wrong  -- E-If-Wrong
ssos (IfThenElse (V Wrong) _ _) = V Wrong
ssos (IfThenElse (V T) t _) = t         -- E-IfTrue
ssos (IfThenElse (V F) _ t) = t         -- E-IfFalse
ssos (IfThenElse t x y) = IfThenElse (ssos t) x y       -- E-If

-- Evaluate using small-step semantics
-- Return a UAE term in normal form
eval :: Term -> Term
eval t = if t == t' then t else eval t'
    where
        t' = ssos t