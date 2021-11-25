module ULC2 where

import ULC

-- Church boolean true
tru :: Term
tru = Lam T $ Lam F $ Var T

-- Church boolean false
fls :: Term
fls = Lam T $ Lam F $ Var F

-- Plus λ-calculus term
plus :: Term
plus = Lam M $ Lam N $ Lam S $ Lam Z $ App (App (Var M) (Var S)) (App (App (Var N) (Var S)) (Var Z))

-- Logical NOT
lnot :: Term -> Term
lnot t = App not' t
    where
        not' = Lam X $ App (App (Var X) fls) tru

-- Logical AND
land :: Term -> Term -> Term
land t1 t2 = App (App and' t1) t2
    where
        and' = Lam X $ Lam Y $ App (App (Var X) (Var Y)) fls

-- Logical OR
lor :: Term -> Term -> Term
lor t1 t2 = App (App or' t1) t2
    where
        or' = Lam X $ Lam Y $ App (App (Var X) (Var X)) (Var Y)

-- Numeric Sum (Addition)
add :: Term -> Term -> Term
add t1 t2 = App (App plus t1) t2

-- Numeric times (Multiplication)
mult :: Term -> Term -> Term
mult t1 t2 = App (App times t1) t2
    where
        times = Lam M $ Lam N $ App (App (Var M) (App plus (Var N))) c0
        c0 = Lam S $ Lam Z $ Var Z

-- Predecessor function
prd :: Term -> Term
prd t = App pred' t
    where
        fst = Lam P $ App (Var P) tru
        snd = Lam Q $ App (Var Q) fls
        pair = Lam F $ Lam S $ Lam B $ App (App (Var B) (Var F)) (Var S)
        c0 = Lam S $ Lam Z $ Var Z
        c1 = Lam S $ Lam Z $ App (Var S) (Var Z)
        ss = Lam P $ App (App pair (App snd (Var P))) (App (App plus c1) (App snd (Var P)))
        zz = App (App pair c0) c0
        pred' = Lam M $ App fst (App (App (Var M) ss) zz)
