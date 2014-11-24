(set-logic HORN)
(set-option :fixedpoint.engine predabst)
;(set-option :produce-proofs true)

(declare-fun __pred__p1 (Int) Bool)
(declare-fun __pred____wf__rank (Int Int) Bool)
(declare-fun __pred__t1 (Int Int) Bool)
(declare-fun __temp__t1 (Int Int Int) Bool)
(declare-fun __temp__extra__e1 (Int) Bool)

(declare-fun p1 (Int) Bool)
(declare-fun __wf__rank (Int Int) Bool)
(declare-fun t1 (Int Int) Bool)


; predicate abstraction definition
(assert (forall ((x Int)) (=> (and (< x 1) (>= x 0)) (__pred__p1 x))))

(assert (forall ((x Int) (xp Int))
	(=> (and (>= x 0) (= xp (+ x 1)) (= xp (+ x 1))) (__pred____wf__rank x xp))))

(assert (forall ((x Int) (xp Int))
	(=> (and (>= x 0) (= xp (- x 1)) (= xp (+ x 1))) (__pred__t1 x xp))))

(assert (forall ((x Int) (y Int) (b Int)) (=> (or (and (= b 0) (= y (+ x 1)))
(and (= b 1) (= y (+ x 2)))) (__temp__t1 x y b))))

(assert (forall ((b Int)) (=> (or (= b 0) (= b 1)) (__temp__extra__e1 b))))

; verification conditions

(assert (forall ((x Int)) (=> (>= x 0) (p1 x))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (p1 xp))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (__wf__rank x xp))))

(check-sat)
;(get-model)
;(get-proof)
