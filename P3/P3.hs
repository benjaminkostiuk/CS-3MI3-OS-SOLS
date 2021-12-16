module P3 where

import Data.List

-- Terms
data T = App T T        -- x y
       | If T T T       -- if x then y else z
       | Succ T         -- succ nv
       | Pred T         -- pred nv
       | IsZero T       -- iszero nv
       | Val V          -- values
       | Let Label T T  -- let x = t1 in t
       | Seq T T        -- t1 ; t2
       | Alloc T        -- ref t
       | DeRef T        -- !t
       | Assign T T     -- t1 := t2
  deriving (Show,Eq)

-- Values
data V = Tru            -- true
    | Fls               -- false
    | Z                 -- zero
    | SuccNV V          -- succ nv
    | UnitV             -- unit
    | Location Loc      -- l
    | Var Label         -- x
    | L Label Type T    -- \x : T. t
    deriving(Show, Eq)

-- Variable names
data Label = A | C | D | E | F | G | H | I | J | K
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
-- Memory location labels
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

-- Types
data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type
    deriving (Show, Eq)

-- Typing Context
type Gamma = [(Label, Type)]
-- Memory Store
type Mu = [(Loc, V)]

-- List of all possible variable names
variables :: [Label]
variables = [A, C, D, E, F, G, H, I, J, K, M, O, P, Q, R, S, U, W, Y]

-- List of all possible memory locations
memoryLocations :: [Loc]
memoryLocations = [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9]

-- Return the list of ALL variables used in a term
vars :: T -> [Label]
vars (Val (Var x)) = [x]
vars (Val (L x _ t)) = [x] `union` vars t
vars (Val (SuccNV nv)) = vars (Val nv)
vars (Val _) = []
vars (App t1 t2) = vars t1 `union` vars t2
vars (If t1 t2 t3) = vars t1 `union` vars t2 `union` vars t3
vars (Succ t) = vars t
vars (Pred t) = vars t
vars (IsZero t) = vars t
vars (Let x t1 t2) = [x] `union` vars t1 `union` vars t2
vars (Seq t1 t2) = vars t1 `union` vars t2
vars (Alloc t) = vars t
vars (DeRef t) = vars t
vars (Assign t1 t2) = vars t1 `union` vars t2

-- Given a list of terms return a variable unused by any term
-- If there is not unused variable throw an error
findUnusedVar :: [T] -> Label
findUnusedVar [] = head variables
findUnusedVar ts
    | available == [] = error "No available unused variables"
    | otherwise = head available
    where
        available = variables \\ (foldr (\t -> union (vars t)) [] ts)

-- Given a memory store with the locations of stored variables return a free memory location
-- If there is not unused memory location throw an error
findUnusedMemLoc :: Mu -> Loc
findUnusedMemLoc [] = head memoryLocations
findUnusedMemLoc mu
    | available == [] = error "No available memory locations"
    | otherwise = head available
    where
        available = memoryLocations \\ (map fst mu)

-- Get the list of free variable labels in a term
freeVars :: T -> [Label]
freeVars (Val (Var x)) = [x]
freeVars (Val (L x _ t)) = freeVars t \\ [x]
freeVars (Val (SuccNV nv)) = freeVars (Val nv)  
freeVars (Val _) = []
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2
freeVars (If t1 t2 t3) = freeVars t1 `union` freeVars t2 `union` freeVars t3
freeVars (Succ t) = freeVars t
freeVars (Pred t) = freeVars t
freeVars (IsZero t) = freeVars t
freeVars (Let x inner outer) = (freeVars outer \\ [x]) `union` freeVars inner
freeVars (Seq t1 t2) = freeVars t1 `union` freeVars t2
freeVars (Alloc t) = freeVars t
freeVars (DeRef t) = freeVars t
freeVars (Assign t1 t2) = freeVars t1 `union` freeVars t2

-- Relabel all bound variables in a term
relabel :: T -> Label -> Label -> T
relabel v@(Val (Var x)) old new = if x == old then Val (Var new) else v
relabel (Val (L x typ t)) old new = if x == old
    then Val (L new typ (relabel t old new)) else Val (L x typ (relabel t old new))
relabel v@(Val (SuccNV nv)) old new = Val (SuccNV nv')
    where
        (Val nv') = relabel (Val nv) old new
relabel v@(Val _) _ _ = v
relabel (App t1 t2) old new = App (relabel t1 old new) (relabel t2 old new)
relabel (If t1 t2 t3) old new = If (relabel t1 old new) (relabel t2 old new) (relabel t3 old new)
relabel (Succ t) old new = Succ $ relabel t old new
relabel (Pred t) old new = Pred $ relabel t old new
relabel (IsZero t) old new = IsZero $ relabel t old new
relabel (Let x inner outer) old new = let
        newIn = relabel inner old new
        newOut = relabel outer old new
    in (if x == old then Let new newIn newOut else Let x newIn newOut)
relabel (Seq t1 t2) old new = Seq (relabel t1 old new) (relabel t2 old new)
relabel (Alloc t) old new = Alloc $ relabel t old new
relabel (DeRef t) old new = DeRef $ relabel t old new
relabel (Assign t1 t2) old new = Assign (relabel t1 old new) (relabel t2 old new)

-- Substitute all instances of a variable for a term in a term
sub :: T -> Label -> T -> T
sub v@(Val (Var x)) var subIn = if x == var then subIn else v
sub l@(Val (L x typ t)) var subIn
    | elem x (freeVars subIn) = Val (L x' typ (sub t' var subIn))   -- Rename bound variable
    | x == var = l                                  -- Do nothing if bound variable == subbed var
    | otherwise = Val (L x typ (sub t var subIn))   -- Simply sub in inner term
    where
        (Val (L x' _ t')) = relabel l x notUsed
        notUsed = findUnusedVar [l, Val (Var var), subIn]   -- Find an unused variable 
sub (Val (SuccNV nv)) var subIn = Val (SuccNV nv')
    where
        (Val nv') = sub (Val nv) var subIn
sub v@(Val _) _ _ = v
sub (App t1 t2) var subIn = App (sub t1 var subIn) (sub t2 var subIn)
sub (If t1 t2 t3) var subIn = If (sub t1 var subIn) (sub t2 var subIn) (sub t3 var subIn)
sub (Succ t) var subIn = Succ $ sub t var subIn
sub (Pred t) var subIn = Pred $ sub t var subIn
sub (IsZero t) var subIn = IsZero $ sub t var subIn
sub (Let x inner outer) var subIn
    | elem x (freeVars subIn) = Let notUsed (sub inner var subIn) (sub outer' var subIn)    -- Rename bound variable
    | x == var = Let x (sub inner var subIn) outer          -- Do nothing to outer bound variable == subbed var
    | otherwise = Let x (sub inner var subIn) (sub outer var subIn) -- Simply sub in outer and inner term
    where
        outer' = relabel outer x notUsed
        notUsed = findUnusedVar [Val (Var x), outer, Val (Var var), subIn]  -- Find unused variable
sub (Seq t1 t2) var subIn = Seq (sub t1 var subIn) (sub t2 var subIn)
sub (Alloc t) var subIn = Alloc $ sub t var subIn
sub (DeRef t) var subIn = DeRef $ sub t var subIn
sub (Assign t1 t2) var subIn = Assign (sub t1 var subIn) (sub t2 var subIn)

-- Check if a term is in a normal form
isNF :: T -> Bool
isNF (Val _) = True
isNF (If (Val Tru) _ _) = False
isNF (If (Val Fls) _ _) = False
isNF (If t _ _) = isNF t
isNF (Succ (Val Z)) = False
isNF (Succ (Val (SuccNV _))) = False
isNF (Succ t) = isNF t
isNF (Pred (Val Z)) = False
isNF (Pred (Val (SuccNV _))) = False
isNF (Pred t) = isNF t
isNF (IsZero (Val Z)) = False
isNF (IsZero (Val (SuccNV _))) = False
isNF (IsZero t) = isNF t
isNF (App (Val (L _ _ _)) _) = False
isNF (App (Val _) (Val (L _ _ _))) = True
isNF (App t1 t2) = isNF t1 && isNF t2
isNF (Let _ (Val _) _) = False
isNF (Let _ t _) = isNF t
isNF (Seq (Val UnitV) _) = False
isNF (Seq t1 _) = isNF t1
isNF (Alloc (Val _)) = False
isNF (Alloc t) = isNF t
isNF (DeRef (Val (Location _))) = False
isNF (DeRef t) = isNF t
isNF (Assign (Val (Location _)) (Val _)) = False
isNF (Assign (Val _) t2) = isNF t2
isNF (Assign t1 t2) = isNF t1

-- Output the result applying a small-step semantics evaluation rule to a term
ssos :: (T, Mu) -> (T, Mu)
ssos v@(Val _, _) = v                           -- Reflexivity of values
-- Booleans
ssos (If (Val Tru) t2 _, mu) = (t2, mu)         -- E-IfTrue
ssos (If (Val Fls) _ t3, mu) = (t3, mu)         -- E-IfFalse
ssos (If t1 t2 t3, mu) = (If t1' t2 t3, mu')    -- E-If
    where 
        (t1', mu') = ssos (t1, mu)
-- Naturals
ssos (Succ (Val nv), mu) = (Val (SuccNV nv), mu)        -- Conversion of Succ to SuccNV for values
ssos (Succ t, mu) = (Succ t', mu')                      -- E-Succ
    where
        (t', mu') = ssos (t, mu)
ssos (Pred (Val Z), mu) = (Val Z, mu)               -- E-PredZero
ssos (Pred (Val (SuccNV nv)), mu) = (Val nv, mu)    -- E-PredSucc
ssos (Pred t, mu) = (Pred t', mu')                  -- E-Pred
    where
        (t' , mu') = ssos (t, mu)
ssos (IsZero (Val Z), mu) = (Val Tru, mu)           -- E-IsZeroZero
ssos (IsZero (Val (SuccNV nv)), mu) = (Val Fls, mu) -- E-IsZeroSucc
ssos (IsZero t, mu) = (IsZero t', mu')              -- E-IsZero
    where
        (t', mu') = ssos (t, mu)
-- Lambda-Calculus
ssos (App (Val (L x typ t)) v@(Val _), mu) = (sub t x v, mu)    -- E-AppAbs
ssos (App v@(Val _) t2, mu) = (App v t2', mu')                  -- E-App2
    where
        (t2', mu') = ssos (t2, mu)
ssos (App t1 t2, mu) = (App t1' t2, mu')                        -- E-App1
    where
        (t1', mu') = ssos (t1, mu)
-- Let Bindings
ssos (Let x v@(Val _) t2, mu) = (sub t2 x v, mu)    -- E-LetV
ssos (Let x t1 t2, mu) = (Let x t1' t2, mu')        -- E-Let
    where
        (t1', mu') = ssos (t1, mu)
-- Sequencing
ssos (Seq (Val UnitV) t2, mu) = (t2, mu)    -- E-SeqNext
ssos (Seq t1 t2, mu) = (Seq t1' t2, mu')    -- E-Seq
    where
        (t1', mu') = ssos (t1, mu)
-- Referencing
ssos (Alloc (Val v), mu) = (Val (Location loc), (loc,v):mu)     -- E-RefV
    where
        loc = findUnusedMemLoc mu    
ssos (Alloc t, mu) = (Alloc t', mu')                            -- E-Ref
    where
        (t', mu') = ssos (t, mu)
ssos (DeRef (Val loc@(Location l)), mu) = (Val v, mu)           -- E-DerefLoc
    where
        v = foldr (\(mem, val) def -> if mem == l then val else def) loc mu
ssos (DeRef t, mu) = (DeRef t', mu')                            -- E-Deref
    where
        (t', mu') = ssos (t, mu)
ssos (Assign (Val (Location l)) (Val v), mu) = (Val UnitV, mu')     -- E-Assign
    where
        mu' = foldr replace [] mu
        replace =  (\m@(mem, val) ms -> if mem == l then (mem, v):ms else m:ms)
ssos (Assign v@(Val _) t2, mu) = (Assign v t2', mu')        -- E-Assign2
    where
        (t2', mu') = ssos (t2, mu)
ssos (Assign t1 t2, mu) = (Assign t1' t2, mu')              -- E-Assign1
    where
        (t1', mu') = ssos (t1, mu)

-- Attempt to type check a term T given a typing context Gamma
-- If typeable return Just Type, otherwise return Nothing
typeCheck :: Gamma -> T -> Maybe Type
-- Booleans
typeCheck _ (Val Tru) = Just BOOL           -- T-True
typeCheck _ (Val Fls) = Just BOOL           -- T-False
typeCheck g (If t1 t2 t3) = if type1 == Just BOOL && type2 == type3     --T-If
        then type2 else Nothing
    where
        type1 = typeCheck g t1
        type2 = typeCheck g t2
        type3 =  typeCheck g t3
-- Naturals
typeCheck _ (Val Z) = Just NAT                          -- T-Zero
typeCheck g (Succ t) = if typeCheck g t == Just NAT     -- T-Succ
        then Just NAT else Nothing
typeCheck g (Val (SuccNV nv)) = Nothing                 -- SuccNV is an internal term and should not type check
typeCheck g (Pred t) = if typeCheck g t == Just NAT     -- T-Pred
        then Just NAT else Nothing
typeCheck g (IsZero t) = if typeCheck g t == Just NAT  -- T-IsZero
    then Just BOOL else Nothing
-- Lambda-Calculus
typeCheck [] (Val (Var _)) = Nothing            -- return Nothing for a free variable 
typeCheck ((label,typ):gs) x@(Val (Var name))   -- T-Var
    | label == name = Just typ
    | otherwise = typeCheck gs x
typeCheck gs (Val (L x typ1 t2)) = case typeCheck ((x, typ1):gs) t2 of    -- T-Abs
        Just typ2 -> Just (Arrow typ1 typ2)
        _ -> Nothing
typeCheck gs (App t1 t2) = case typeCheck gs t1 of      -- T-App
        Just (Arrow typ1 typ2) -> if typeCheck gs t2 == Just typ1 then Just typ2 else Nothing
        _ -> Nothing
-- Unit
typeCheck _ (Val UnitV) = Just Unit     -- T-Unit
-- Let Bindings
typeCheck gs (Let x (Alloc r) t2) = case typeCheck gs r of    -- T-Ref + T-Let (only allow ref directly inside of let)
        Just typ1 -> typeCheck ((x, Ref typ1):gs) t2
        _ -> Nothing
typeCheck gs (Let x t1 t2) = case typeCheck gs t1 of    -- T-Let
        Just typ1 -> typeCheck ((x, typ1):gs) t2 
        _ -> Nothing
-- Sequencing
typeCheck gs (Seq t1 t2)                 -- T-Seq
    | typeCheck gs t1 == Just Unit && typ2 /= Nothing = typ2
    | otherwise = Nothing
        where
            typ2 = typeCheck gs t2
-- Referencing
typeCheck _ (Val (Location _)) = Nothing    -- Locations are part of the internal calculus, thus are not well typed
typeCheck gs (Alloc _) = Nothing            -- Do not allow ref to be used outside let
typeCheck gs (DeRef t) = case typeCheck gs t of         -- T-Deref
        Just (Ref typ) -> Just typ
        _ -> Nothing
typeCheck gs (Assign t1 t2) = case typeCheck gs t1 of   -- T-Assign
        Just (Ref typ1) -> if typeCheck gs t2 == Just typ1 then Just Unit else Nothing  
        _ -> Nothing

-- Evaluate a terms down to its normal form
eval :: T -> T
eval t = evalWithMu (t, [])
    where
        evalWithMu :: (T, Mu) -> T
        evalWithMu (t', mu)
            | isNF t' = t'
            | otherwise = evalWithMu $ ssos (t', mu)

-- TypeCheck and fully evaluate a term
run :: T -> T
run t = maybe (error errStr) (\_ -> eval t) (typeCheck [] t)
    where
        errStr = "Error! Typechecking Failed!"