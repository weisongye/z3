(set-logic HORN)
(set-option :fixedpoint.engine predabst)
;(set-option :produce-proofs true)

(declare-fun __pred__p1 (Int) Bool)
(declare-fun __pred____wf__rank (Int Int) Bool)
(declare-fun __pred__t1 (Int Int) Bool)

(declare-fun p1 (Int) Bool)
(declare-fun __wf__rank (Int Int) Bool)
(declare-fun t1 (Int Int) Bool)


; predicate abstraction definition
(assert (forall ((x Int)) (=> (and (< x 1) (>= x 0)) (__pred__p1 x))))

(assert (forall ((x Int) (xp Int))
	(=> (and (>= x 0) (= xp (+ x 1)) (= xp (+ x 1))) (__pred____wf__rank x xp))))

;(assert (forall ((x Int) (xp Int)) (=> (and (>= x 0) (= xp (- x 1)) (= xp (+ x 1))) (__pred__t1 x xp))))

; verification conditions

(assert (forall ((x Int)) (=> (>= x 0) (p1 x))))

(assert (forall ((x Int) (xp Int)) (=> (and (>= x 0) (= xp (- x 1))) (t1 x xp))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (p1 xp))))

(assert (forall ((x Int) (xp Int)) (=> (and (p1 x) (t1 x xp)) (__wf__rank x xp))))

(check-sat)
;(get-model)
;(get-proof)
