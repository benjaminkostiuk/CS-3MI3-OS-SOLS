module UAE3 where

import UAE2

-- Big step semantics
bsos :: Term -> Term
bsos (V x) = V x        -- B-Value
bsos (NV x) = NV x      -- B-Value
-- B-Succ
bsos (Succ t) = case bsos t of (NV x) -> NV $ SuccVal x
                               _ -> V Wrong
-- B-PredZero + B-PredSucc
bsos (Pred t) = case bsos t of (NV Z) -> NV Z
                               (NV (SuccVal nv)) -> NV nv
                               _ -> V Wrong
-- B-IsZeroZero + B-IsZeroSucc
bsos (IsZero t) = case bsos t of (NV Z) -> V T
                                 (NV (SuccVal nv)) -> V F
                                 _ -> V Wrong
-- B-IfTrue + B-IfFalse
bsos (IfThenElse t1 t2 t3) = case bsos t1 of (V T) -> bsos t2
                                             (V F) -> bsos t3
                                             _ -> V Wrong