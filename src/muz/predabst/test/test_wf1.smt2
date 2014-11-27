(set-logic HORN)
(set-option :fixedpoint.engine predabst)

(declare-fun p1 (Int) Bool)
(declare-fun __wf__rank (Int Int) Bool)
(declare-fun t1 (Int Int) Bool)

; verification conditions

(assert (forall ((x Int)) (=> (>= x 0) (p1 x))))

(assert (forall ((x Int) (xp Int)) (=> (and (>= x 0) (= xp (- x 1))) (t1 x xp))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (p1 xp))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (__wf__rank x xp))))

(check-sat)
