(set-logic HORN)
(set-option :fixedpoint.engine predabst)

(declare-fun __pred__p1 (Int Int Int) Bool)
(declare-fun __pred__p2 (Int Int Int) Bool)
(declare-fun __pred__p3 (Int Int Int) Bool)
(declare-fun __pred__p4 (Int Int Int) Bool)
(declare-fun __pred__p5 (Int Int Int) Bool)

(declare-fun p1 (Int Int Int) Bool)
(declare-fun p2 (Int Int Int) Bool)
(declare-fun p3 (Int Int Int) Bool)
(declare-fun p4 (Int Int Int) Bool)
(declare-fun p5 (Int Int Int) Bool)
;(declare-fun p6 (Int Int Int) Bool)

; predicate abstraction definition
(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (= x 2) ;(>= x y) (>= y z)
	) (__pred__p2 x y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (= x 3) (>= x y) (>= y z)) (__pred__p3 x y z))))

; verification conditions
(assert (forall ((x Int) (y Int) (z Int))
	(=> true (p1 x y z))))

;(assert (forall ((x Int) (y Int) (z Int))
;	(=> (p6 x y z) (p1 x y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (>= y z) (p1 x y z)) 
	(p2 x y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (>= y z) (p2 x y z))
	(p2 (+ x 1) y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (>= x y) (p2 x y z)) 
	(p3 x y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (>= x z) (p3 x y z))
	(p4 x y z))))

(assert (forall ((x Int) (y Int) (z Int))
	(=> (and (not (>= x z)) (p3 x y z))
	(p5 x y z))))

(assert (forall ((x Int) (y Int) (z Int)) (=> (p5 x y z) (= x y))))

(check-sat)
