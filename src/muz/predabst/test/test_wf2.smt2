(set-logic HORN)
(set-option :fixedpoint.engine predabst)
;(set-option :produce-proofs true)

(declare-fun __pred__p1 (Int Int) Bool)
(declare-fun __pred____wf__rank (Int Int Int Int) Bool)
(declare-fun __pred____t1 (Int Int Int Int) Bool)

(declare-fun p1 (Int Int) Bool)
(declare-fun __wf__rank (Int Int Int Int) Bool)
(declare-fun t1 (Int Int Int Int) Bool)


; predicate abstraction definition
(assert (forall ((x Int) (y Int)) (=> (>= x y) (__pred__p1 x y))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
	(=> (and (>= x y) (= xp (- x 1)) (= xp (+ x 1)) (= yp y)) (__pred____wf__rank x y xp yp))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
	(=> (and (>= x y) (= xp (- x 1)) (= xp (+ x 1)) (= yp y)) (__pred____t1 x y xp yp))))

; verification conditions

(assert (forall ((x Int) (y Int)) (=> (>= x y) (p1 x y))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int)) (=> (and (= xp (+ x 1)) (= yp y)) (t1 x y xp yp))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int)) (=> (and (p1 x y) (t1 x y xp yp)) (p1 xp yp))))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int))
	(=> (and (>= x y) (= xp (- x 1)) (= yp y) (p1 x y)) 
	(__wf__rank x y xp yp))))

(check-sat)
;(get-model)
;(get-proof)
