module ULCTest where

import ULC

a1 = Var A
a2 = App (Var A) (Var A)
a3 = App (App (Var A) (Var B)) (Var C)
a4 = App (Var A) (Lam B (Var B))
a5 = App (Lam A (Var A)) (Var A)
a6 = App (Lam A (Var B)) (App (Var B) (Var C))
a7 = App (Var X) (App (Lam A (Var A)) (Lam B (Var B)))
a8 = App (Lam Y (Lam Y (App (Var X) (Var Y)))) (App (Var Y) (Var Z))
a9 = App (Lam Y (Lam W (App (Var X) (Var Y)))) (App (Var Y) (Var Z))
a10 = App (Lam Y (Lam W (App (Var W) (Var Y)))) (App (Var Y) (Var W))
l1 = Lam A $ Var A
l2 = Lam B $ Var A
l3 = App (Lam B (Var A)) (Lam C (Var A))
l4 = App (Lam A (Var A)) (Lam C (Var A))
l5 = App (Lam A (Var A)) (Lam A (Var A))
l6 = App (Lam A (Lam A (App (Var A) (Var B)))) (Lam C (Var C))
l7 = Lam C $ Var C
l8 = Lam Y $ App (Var X) (Var Y)
l9 = Lam Z $ App (Lam A (Var A)) (Lam B (Var B))
l10 = App (Lam A (Var A)) (App (Lam B (Var B)) (Var B))

t1 = fv a1 == [A]
t2 = fv l1 == []
t3 = fv l2 == [A]
t4 = fv l4 == [A]
t5 = fv a2 == [A]
t6 = fv a3 == [A, B, C]

t7 = relabel l1 A B == (Lam B (Var B))
t8 = relabel l1 A A == l1
t9 = relabel l1 C A == l1
t10 = relabel l5 A B == App (Lam B (Var B)) (Lam B (Var B))
t11 = relabel (relabel l6 A C) C D == App (Lam D (Lam D (App (Var D) (Var B)))) (Lam D (Var D))

t12 = sub l4 B (Var A) == App (Lam C (Var C)) (Lam C (Var A))
t13 = sub l4 B (Var Z) == l4
t14 = sub a1 A (Var B) == Var B
t15 = sub (sub a3 A (Var X)) B (Var Y) == App (App (Var X) (Var Y)) (Var C)
t16 = sub a2 C (Var A) == a2
t17 = sub a2 B (Var Z) == a2
t18 = sub l1 A (Var B) == l7
t19 = sub l7 A (Var Z) == l7
t20 = sub l8 X (App (Var X) (Var Y)) == Lam A (App (App (Var X) (Var Y)) (Var A))
t21 = sub l8 Y (App (Var X) (Var Y)) == Lam A (App (Var X) (Var A))

t30 = isNF a1
t31 = isNF a2
t32 = isNF a4
t33 = isNF a3
t34 = not $ isNF a5
t35 = not $ isNF a6
t36 = isNF l1
t37 = not $ isNF l3
t38 = isNF l8
t39 = isNF l9
t40 = not $ isNF a7

t50 = ssos a1 == a1
t51 = ssos a2 == a2
t52 = ssos a4 == a4
t53 = ssos l2 == l2
t54 = ssos a5 == Var A
t55 = ssos a6 == Var B
t56 = ssos a8 == Lam A (App (Var X) (Var A))
t57 = ssos a9 == Lam W (App (Var X) (App (Var Y) (Var Z)))
t58 = ssos a10 == Lam A (App (Var A) (App (Var Y) (Var W)))
t59 = ssos l10 == App (Lam A (Var A)) (Var B)

t70 = eval a7 == App (Var X) (Lam B (Var B))
t71 = eval a8 == Lam A (App (Var X) (Var A))
t72 = eval a9 == Lam W (App (Var X) (App (Var Y) (Var Z)))
t73 = eval a10 == Lam A (App (Var A) (App (Var Y) (Var W)))
t74 = eval l3 == Var A
t75 = eval l4 == Lam C (Var A)
t76 = eval l6 == Lam D (App (Var D) (Var B))
t77 = eval l10 == Var B
