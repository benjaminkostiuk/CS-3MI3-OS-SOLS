module P3Test where

import P3

-- Tests if a term evaluates to a term and typeChecks as a type
test :: T -> T -> Maybe Type -> Bool
test t exp typ = eval t == exp && typeCheck [] t == typ

-- Run this to check if any test cases fail
-- Prints the names of all failed test cases
failed :: String
failed = "Cases failed:" ++ foldr (\(x, _) s -> " t" ++ show x ++ s) "" failedCases
    where
        failedCases = filter (not . snd) (zip [1..] cases)

cases = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,
    t11, t21, t13, t14, t15, t16, t17, t18, t19, t20,
    t21, t22, t23, t24, t25, t26, t27, t28, t29, t30,
    t31, t32, t33, t34, t35, t36, t37, t38, t39, t40,
    t41, t42, t43, t44, t45, t46, t47, t48, t49, t50,
    t51, t52, t53, t54, t55, t56, t57, t58, t59, t60,
    t61, t62, t63, t64, t65, t66]

-- Booleans and Naturals ------------
true = Val Tru
false = Val Fls
zero = Val Z
-- Some variables
x = Val (Var X)
y = Val (Var Y)
a = Val (Var A)
c = Val (Var C)
d = Val (Var D)
e = Val (Var E)

-- Numeric values
numVal :: Int -> T
numVal 0 = zero
numVal x = Val (SuccNV nv)
    where
        (Val nv) = numVal (x-1)

-- Numeric terms
num :: Int -> T
num 0 = zero
num n = Succ $ num (n - 1)

-- Booleans and Naturals -----------
b1 = If true false true
b2 = If true zero false
b3 = If (If false true false) true false
b4 = If (IsZero (Pred zero)) (num 3) (num 2)
b5 = If (IsZero (Pred (Pred (num 3)))) (num 4) (Pred (num 17))

n1 = Succ $ Succ $ Succ $ Succ $ IsZero (Val Z)
n2 = Pred $ Pred $ Succ $ Pred $ Pred $ Succ $ Pred $ (If (IsZero (num 17)) (num 4) (num 1))
n3 = IsZero $ Succ $ If false (numVal 4) (Pred true) 
n4 = IsZero $ Succ $ If false (num 4) (Pred zero)
n5 = If (Pred true) (numVal 3) (num 5)
n6 = Succ $ Succ $ Pred (numVal 4)

t0 = test b1 false (Just BOOL)
t1 = test b3 false (Just BOOL)
t2 = typeCheck [] b2 == Nothing
t3 = test b4 (numVal 3) (Just NAT)
t4 = typeCheck [] n1 == Nothing
t5 = test n2 zero (Just NAT)
t6 = typeCheck [] n3 == Nothing
t7 = test n4 false (Just BOOL)
t8 = typeCheck [] n5 == Nothing
t9 = typeCheck [] n6 == Nothing
t10 = test b5 (numVal 16) (Just NAT)

--- Lambda Calculus --------------
l1 = Val $ L X NAT x
l2 = Val $ L Y NAT (Val (L X BOOL y))
l3 = Val $ L Y NAT (Val (L X BOOL (Val (L A NAT c))))
l4 = Val $ L Y BOOL (Val (L Y NAT (Succ y)))
l5 = App (Val (L Y BOOL l5a)) false
l5a = App (App (Val (L X NAT (Val (L Y NAT (Succ (Val (Var Y))))))) zero) (num 7)
l6 = App (Val (L Y (Arrow NAT BOOL) (App y l6a))) (Val (L X NAT (IsZero x)))
l6a = App (App (Val (L X NAT (Val (L Y NAT (Pred (Val (Var X))))))) zero) (num 9)
l7 = App (Val (L Y NAT (Val (L Y (Arrow BOOL BOOL) y)))) (num 8)
l8 = App (App (Val (L Y NAT (Val (L Y (Arrow BOOL BOOL) y)))) (num 8)) false
l9 = App (App (Val (L Y (Arrow NAT BOOL) l9a)) (Val (L X NAT (IsZero x)))) zero
l9a = Val (L A NAT (App y a))
l10 = Val $ L X (Arrow BOOL NAT) (App x false)
l11 = App (Val (L Y (Arrow NAT NAT) (num 5))) (App (App l11a zero) true)
l11a = Val $ L Y NAT $ Val $ L X BOOL $ Val $ L Y NAT y
l12 = App (Val (L A (Arrow NAT NAT) (App a (num 2)))) (Val (L A NAT (Pred a)))
l13 = App (Val (L A (Arrow NAT NAT) (Val (L C NAT (App a c))))) c
l14 = App (App l14a (Val $ L Y NAT (IsZero y))) zero   
l14a = Val $ L Y (Arrow NAT BOOL) $ Val $ L Y NAT $ Val $ L Y (Arrow BOOL NAT) $ Val $ L Y NAT y
l15 = App (App (App (App l14a (Val (L Y NAT (IsZero y)))) zero) (Val (L Y BOOL zero))) (num 17)
l16 = App (Val (L X NAT (IsZero (Pred (Pred (Succ (Pred (Succ (Val (SuccNV (Var X))))))))))) (num 2)
l17 = App (App l17a zero) (Val (L X NAT (Succ x)))  
l17a = Val $ L Y NAT $ Val $ L X (Arrow NAT NAT) $ App x (App x (App x y))
l18 = App (App l17a zero) (Val (L X NAT (Pred x)))

t11 = test l1 l1 (Just (Arrow NAT NAT))
t12 = test l2 l2 (Just (Arrow NAT (Arrow BOOL NAT)))
t13 = typeCheck [] l3 == Nothing
t14 = test l4 l4 (Just (Arrow BOOL (Arrow NAT NAT)))
t15 = test l5 (numVal 8) (Just NAT)
t16 = test l6 true (Just BOOL)
t17 = test l7 (Val (L Y (Arrow BOOL BOOL) y)) (Just (Arrow (Arrow BOOL BOOL) (Arrow BOOL BOOL)))
t18 = typeCheck [] l8 == Nothing
t19 = typeCheck [] l10 == Just (Arrow (Arrow BOOL NAT) NAT)
-- some substitution test cases
t20 = test l9 true (Just BOOL)          -- Basic sub
t21 = test l11 (numVal 5) (Just NAT)    -- Sub y /= x
-- MIGHT NOT WORK FOR ALL RENAMING IMPLEMENTATIONS
t22 = test l13 (Val (L D NAT (App c d))) Nothing    -- Sub with y in FV (Uses strategy to pick first not used variable)
t23 = test l14 (Val (L Y (Arrow BOOL NAT) (Val (L Y NAT y)))) (Just (Arrow (Arrow BOOL NAT) (Arrow NAT NAT)))  -- Sub with x == y
t24 = test l15 (numVal 17) (Just NAT)
t25 = test l12 (numVal 1) (Just NAT)                -- Sub with App
t26 = typeCheck [] l16 == Nothing
t27 = test l17 (numVal 3) (Just NAT)
t28 = test l18 zero (Just NAT)

---- Unit -----
unit = Val UnitV
u1 = App (Val (L X Unit (Val (L X Unit zero)))) unit
u2 = Val $ L X Unit $ App x zero
u3 = Val $ L X (Arrow Unit BOOL) $ App x (If (IsZero (Succ unit)) unit unit)
u4 = Val $ L X (Arrow Unit BOOL) $ App x (If (App x unit) unit unit)

t29 = test u1 (Val (L X Unit zero)) (Just (Arrow Unit NAT))
t30 = typeCheck [] u2 == Nothing
t31 = typeCheck [] u3 == Nothing
t32 = test u4 u4 (Just (Arrow (Arrow Unit BOOL) BOOL))

---- Let Bindings -----
lt1 = Let X (num 5) $ Succ $ Succ $ Succ $ Succ $ Succ x
lt2 = Let Y true $ Let Y zero $ IsZero y
lt3 = Let X (IsZero zero) $ Val $ L X (Arrow BOOL BOOL) a
lt4 = Val $ L X (Arrow BOOL NAT) $ Let X (Pred (num 6)) $ Let Y (Val (L Y NAT (Succ y))) $ App y x 
lt5 = Val $ L X (Arrow BOOL NAT) $ Let X (Pred (numVal 6)) $ Let Y (Val (L Y NAT (Succ y))) $ App x y
lt6 = Let X (Pred (Pred (Pred (num 4)))) $ App (Let X (Val (L X NAT (IsZero x))) x) x
lt7 = Let A (If (IsZero false) (numVal 4) (num 3)) $ IsZero $ num 7 
lt8 = App (Let Y lt8a (Val (L A NAT (App y a)))) zero
lt8a = Val (L X NAT (IsZero x))
lt9 = Let Y (App (App l11a zero) true) $ num 5
lt10 = Let A c $ Val (L C NAT (App a c))
lt11 = App (Let Y (Val $ L Y NAT (IsZero y)) lt11a) unit
lt11a = Val $ L Y Unit $ Val $ L Y (Arrow Unit NAT) $ Val $ L Y NAT y
lt12 = Let D (Val $ L Y NAT (Val (L X BOOL (Val (L C NAT a))))) lt12a
lt12a = Let A (num 4) $ Val $ L C (Arrow NAT BOOL) $ App c $ Succ $ Val $ Var A
lt13 = Let A lt13a lt13b
lt13a = Val $ L Y (Arrow Unit Unit) $ Val $ L X BOOL $ Val $ L A NAT unit
lt13b = Let A (num 4) $ Val $ L C (Arrow NAT BOOL) $ App c $ Succ $ Val $ Var A

t33 = test lt1 (numVal 10) (Just NAT)
t34 = test lt2 true (Just BOOL)
t35 = typeCheck [] lt3 == Nothing
t36 = test lt4 lt4 $ Just $ Arrow (Arrow BOOL NAT) NAT
t37 = typeCheck [] lt5 == Nothing
t38 = test lt6 false $ Just BOOL
t39 = test lt7 lt7 Nothing
t40 = test lt8 true (Just BOOL)         -- Basic sub
t41 = test lt9 (numVal 5) (Just NAT)    -- Sub y /= x
-- MIGHT NOT WORK FOR ALL RENAMING IMPLEMENTATIONS
t42 = test lt10 (Val (L D NAT (App c d))) Nothing -- Sub with y in FV (Uses strategy to pick first not used variable)
t43 = test lt11 (Val $ L Y (Arrow Unit NAT) $ Val $ L Y NAT y) $ Just $ Arrow (Arrow Unit NAT) (Arrow NAT NAT)
-- These ones are wierd cause you sub a value into a lambda (then you can't eval anymore)
t44 = test lt12 (Val (L C (Arrow NAT BOOL) (App c (Succ (numVal 4))))) Nothing      -- Checks free variable a
t45 = test lt13 (Val (L C (Arrow NAT BOOL) (App c (Succ (numVal 4))))) $ Just $ Arrow (Arrow NAT BOOL) BOOL

---- Sequencing -----
s1 = Seq (App (Val (L X Unit x)) unit) (Val (L X NAT x))
s2 = Val $ L Y (Arrow NAT Unit) $ Seq (App y (num 7)) (Seq (Let Y (Val (L Y BOOL (If y unit unit))) (App y false)) y)
s3 = Seq (Let Y (Val (L Y Unit true)) (App y unit)) (Seq unit (IsZero (num 4)))
s4 = App (App (Val (L X (Arrow Unit NAT) (Val (L Y BOOL s4a)))) (Val (L A Unit (Seq a (If (IsZero (num 2)) (num 4) (num 6)))))) s4b
s4a = If y (num 0) (App x (Seq unit unit))
s4b = IsZero (Seq (If false unit (App (Val (L X Unit x)) unit)) (num 4))
s5 = App (Val (L A (Arrow BOOL NAT) (Val (L C (Arrow BOOL Unit) s5b)))) c
s5b = Seq (If (IsZero (App a false)) (App c true) (App c false)) (Let C unit (App a (IsZero (Pred (num 4)))))
s5c = Seq (If (IsZero (App c false)) (App d true) (App d false)) (Let D unit (App c (IsZero (Pred (num 4)))))

t46 = test s1 (Val (L X NAT x)) $ Just $ Arrow NAT NAT
t47 = test s2 s2 $ Just $ Arrow (Arrow NAT Unit) (Arrow NAT Unit)
t48 = test s3 (Seq true (Seq unit (IsZero (num 4)))) Nothing
t49 = test s4 (numVal 6) $ Just NAT
t50 = eval s5 == Val (L D (Arrow BOOL Unit) s5c)
    && typeCheck [(C, Arrow BOOL NAT)] s5 == Just (Arrow (Arrow BOOL Unit) NAT)

----- Referencing -------
r1 = Let C (Assign (Val (Location L1)) (num 2)) (Val $ L X (Arrow Unit BOOL) (App x c))
r2 = App (Val (L X NAT (If (IsZero x) (num 3) (num 2)))) (DeRef (Val (Location L1)))
r3 = Seq (Assign (Alloc (num 2)) (num 3)) (num 3)
r4 = App (Let X (DeRef (Alloc true)) (Val (L Y NAT y))) (num 4)
r5 = App (Val (L X (Ref BOOL) (Seq (Assign x false) (DeRef x)))) (Alloc true)
-- Basic cases
r6 = Let X (Alloc (Val (L X NAT (Succ x)))) $ App (DeRef x) (num 3)
r7 = Let X (Alloc (num 4)) $ Seq (Assign x (Succ (DeRef x))) (DeRef x)
r8 = Let Y (Alloc (App (Val (L X (Arrow NAT Unit) x)) (Val (L Y NAT unit)))) $ Seq (Assign y r8a) (App (DeRef y) (num 2))
r8a = Val $ L X (Arrow Unit NAT) x
r9 = Let Y (Alloc (App (Val (L X (Arrow NAT NAT) x)) (Val (L Y NAT (num 3))))) $ Seq (Assign y r9a) (App (DeRef y) (num 2))
r9a = App (Val (L Y (Arrow NAT NAT) (Val (L X NAT (Succ (App y zero)))))) (DeRef y)
r10 = Let Y (Alloc (Val (L A BOOL false))) $ If (Let Y (Alloc (App (DeRef y) true)) (DeRef y)) (Val (L X BOOL (IsZero (num 2)))) (DeRef y) 
r11 = Let Y (Alloc (num 2)) $ If (Seq (Assign y zero) (IsZero (DeRef y))) (Succ (Succ (Seq (Assign y (num 2)) (DeRef y)))) zero
r12 = Let X (Alloc (Val (L X NAT (Pred x)))) $ App (DeRef x) (Seq (Assign x (Val (L X NAT (Succ (Succ x))))) (num 1))
r13 = Let X (Alloc (Val (L X NAT (Pred x)))) $ App (Seq (Assign x (Val (L X NAT (Succ (Succ x))))) r13a) (DeRef x)
r13a = Val $ L X (Arrow NAT NAT) $ App x (num 1)
r14 = Let X (Alloc true) $ Seq (Assign x false) (If (DeRef x) zero (Let Y (Seq (Assign x true) (Pred (num 3))) (If (DeRef x) (num 7) (num 4))))
r15 = Let X (Alloc (Val (L X (Arrow NAT BOOL) (App x zero)))) $ Let Y (Alloc (Val (L Y (Arrow BOOL NAT) (App y false)))) $ App (DeRef x) (Val (L X BOOL zero))
r16 = Let X (Alloc (num 4)) $ If (Let X (Alloc (num 3)) (Seq (Assign x zero) (IsZero (DeRef x)))) (IsZero (DeRef x)) true

-- Location typing
t51 = typeCheck [] r1 == Nothing
t52 = typeCheck [] r2 == Nothing
-- Referencing typing
t53 = typeCheck [] r3 == Nothing
t54 = typeCheck [] r4 == Nothing
t55 = typeCheck [] r5 == Nothing
-- Basic cases
t56 = test r6 (numVal 4) $ Just NAT
t57 = test r7 (numVal 5) $ Just NAT
t58 = typeCheck [] r8 == Nothing
t59 = test r9 (numVal 4) $ Just NAT
-- Other cases
t60 = test r10 (Val (L A BOOL false)) $ Just $ Arrow BOOL BOOL      -- Check multiple indented refs
t61 = test r11 (numVal 4) $ Just NAT        -- Test mu passing in other inference rules
t62 = test r12 zero $ Just NAT
t63 = test r13 (numVal 3) $ Just NAT
t64 = test r14 (numVal 7) $ Just NAT
t65 = typeCheck [] r15 == Nothing    -- deref on a mem location that has incorrect type
t66 = test r16 false $ Just BOOL