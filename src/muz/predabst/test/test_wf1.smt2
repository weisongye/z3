(set-logic HORN)
(set-option :fixedpoint.engine predabst)
;(set-option :produce-proofs true)

(declare-fun __pred__p2 (Int Int) Bool)
(declare-fun __pred____wf__p3 (Int Int Int Int) Bool)

(declare-fun p1 (Int Int) Bool)
(declare-fun p2 (Int Int) Bool)
(declare-fun __wf__p3 (Int Int Int Int) Bool)

; predicate abstraction definition
(assert (forall ((x Int) (y Int)) (=> (>= x y) (__pred__p2 x y))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
	(=> (and (>= x y) (= xp (- x 1)) (= yp y)) (__pred____wf__p3 x y xp yp))))

; verification conditions
(assert (forall ((x Int) (y Int)) (=> true (p1 x y))))

(assert (forall ((x Int) (y Int)) (=> (and (>= x y) (p1 x y)) (p2 x y))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
	(=> (and (>= x y) (= xp (- x 1)) (= yp y) (p2 x y)) 
	(__wf__p3 x y xp yp))))

(check-sat)
;(get-model)
;(get-proof)
