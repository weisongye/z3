(set-logic HORN)
(set-option :fixedpoint.engine predabst)

(declare-fun p1 (Int) Bool)
(declare-fun t1 (Int Int) Bool)

; verification conditions
(assert (forall ((x Int)) (=> (= x 0) (p1 x))))
(assert (forall ((x Int) (y Int)) (=> (= y (+ x 1)) (t1 x y))))
(assert (forall ((x Int) (y Int)) (=> (and (p1 x) (t1 x y)) (p1 y))))
(assert (forall ((x Int)) (=> (p1 x) (>= x 0))))

(check-sat)



