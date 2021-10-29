module UAETest where

import UAE3
import UAE2
import Test.QuickCheck

true = V T
false = V F
wrong = V Wrong
zero = NV Z

-- Convert int to nv
num :: Int -> Term
num 0 = NV Z
num x = NV $ SuccVal y
    where
        (NV y) = num (x - 1)

numNV :: Int -> NumVal
numNV x = let (NV nv) = num x in nv
        
-- QuickCheck
instance Arbitrary Val where
    arbitrary = frequency [(4, pure Wrong), (10, pure T), (10, pure F)]

instance Arbitrary NumVal where
    arbitrary = frequency [(4, pure Z), (6, more)]
        where
            more = do
                n <- getPositive <$> arbitrary
                return $ numNV n

-- Play around with the freuquencies to generate different terms
instance Arbitrary Term where
    arbitrary = frequency [
        (2, V <$> arbitrary),
        (2, NV <$> arbitrary),
        (5, Pred <$> arbitrary),
        (6, Succ <$> arbitrary),
        (5, IsZero <$> arbitrary),
        (3, ifthenelse)
        ]
        where
            ifthenelse = do
                t1 <- arbitrary
                t2 <- arbitrary
                t3 <- arbitrary
                return $ IfThenElse t1 t2 t3

-- View sample with
-- head <$> sample' (arbitrary::Gen Term)

-- Run `quickCheck stepProp` to check this property 
stepProp :: Term -> Bool
stepProp t = eval t == bsos t

-- Manual test cases
type TestCase = (Term, Term)

-- Usage: test eval tx
--        test bsos tx
test :: (Term -> Term) -> TestCase -> Bool
test f (input, expectedOutput) = f input == expectedOutput

x = Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ NV Z
y = IfThenElse (IsZero (Succ (NV Z))) (V T) (Succ (NV Z))
z = IsZero $ V T

t1 = (true, true)
t2 = (false, false)
t3 = (wrong, wrong)
t4 = (zero, zero)
t5 = (num 3, num 3)

t6 = ((Pred (num 4)), num 3)
t7 = ((Pred (num 0)), num 0)
t8 = ((Pred true), wrong)
t9 = ((Pred (IfThenElse (Pred true) (num 2) (num 3))), wrong)
t10 = (x, num 3)
t11 = (Pred (Pred (Pred false)), wrong)
t12 = (Pred (Succ (NV Z)), zero)

t13 = (Succ (Succ (Succ (Succ (Pred (num 0))))), num 4)
t14 = (Succ (Succ true), wrong)
t15 = (Succ (Succ (Succ (IfThenElse false (num 2) (num 3)))), num 6)
t16 = (Succ (Succ (Succ (IfThenElse (num 5) (num 2) (num 3)))), wrong)
t17 = (Succ (IsZero false), wrong)
t18 = (Succ (IsZero (num 0)), wrong)

t19 = (IsZero false, wrong)
t20 = (IsZero zero, true)
t21 = (IsZero (Succ (Pred zero)), false)
t22 = (IsZero (Pred (Succ zero)), true)
t23 = (IsZero (Pred (Pred (Pred (Succ (Succ (num 1)))))), true)
t24 = (IsZero (num 4), false)
t25 = (IsZero (IsZero zero), wrong)

t26 = (y, num 1)
t27 = (IfThenElse zero true false, wrong)
t28 = (IfThenElse (num 3) false true, wrong)
t29 = (IfThenElse (Pred true) true false, wrong)
t30 = (IfThenElse true (num 3) (num 4), num 3)
t31 = (IfThenElse false (num 3) (num 4), num 4)
t32 = (IfThenElse (IsZero (Pred zero)) true (num 4), true)
t33 = (IfThenElse (IsZero (Succ zero)) (num 7) false, false)
t34 = (IfThenElse (IsZero (Pred (Succ zero))) (num 2) (Pred true), num 2)
t35 = (IfThenElse (IsZero (Succ (Pred zero))) (Pred false) (num 3), num 3)