(set-logic HORN)
(set-option :fixedpoint.engine predabst)
;(set-option :produce-proofs true)

(declare-const c Int)
(declare-fun __pred__p1 (Int) Bool)
(declare-fun __pred__t1 (Int Int) Bool)
(declare-fun __temp__t1 (Int Int Int) Bool)
(declare-fun __temp__extra__e1 (Int) Bool)

(declare-fun p1 (Int) Bool)
(declare-fun t1 (Int Int) Bool)

; predicate abstraction definition
(assert (forall ((x Int)) (=> (and (>= x 0) (<= x 0)) (__pred__p1 x))))
(assert (forall ((x Int) (y Int))
(=> (and (= y (- x 2)) (= y (- x 1))) (__pred__t1 x y))))
(assert (forall ((x Int) (y Int) (b Int)) (=> (or (and (= b 0) (= y (+ x 1)))
(and (= b 1) (= y (+ x 2)))) (__temp__t1 x y b))))
(assert (forall ((b Int)) (=> (or (= b 0) (= b 1)) (__temp__extra__e1 b))))

; verification conditions
(assert (forall ((x Int)) (=> (= x 0) (p1 x))))
(assert (forall ((x Int) (y Int)) (=> (and (p1 x) (t1 x y)) (p1 y))))
(assert (forall ((x Int)) (=> (p1 x) (>= x 0))))

(check-sat)
;(get-model)
;(get-proof)




