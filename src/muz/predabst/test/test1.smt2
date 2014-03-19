(set-logic HORN)
(set-option :fixedpoint.engine predabst)

(declare-fun bs2 (Bool Bool Bool Bool) Bool)
(declare-fun bs4 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(assert (forall ((x1 Bool) (x2 Bool)) 
	(=> (=> x1 x2) (bs2 x1 x2 x1 x2))) )
(assert (forall ((x1 Bool) (x2 Bool)) 
	(=> (=> x2 x1) (bs2 x1 x2 x2 x1))) )

(assert (forall ((i1 Bool) (i2 Bool) (i3 Bool) (i4 Bool) 
					(a1 Bool) (a2 Bool) (a3 Bool) (a4 Bool)
					(b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)
					(o1 Bool) (o2 Bool) (o3 Bool) (o4 Bool)) 
	(=> (and 
		(bs2 i1 i2 a1 a2) 
		(bs2 i4 i3 a4 a3) 
		(bs2 a1 a3 b1 b3) 
		(bs2 a2 a4 b2 b4) 
		(bs2 b1 b2 o1 o2) 
		(bs2 b3 b4 o3 o4) 
	) 
	(bs4 i1 i2 i3 i4 o1 o2 o3 o4))) )

(assert (=> (exists (
		(i1 Bool) (i2 Bool) (i3 Bool) (i4 Bool) 
		(o1 Bool) (o2 Bool) (o3 Bool) (o4 Bool)) 
	(and (bs4 i1 i2 i3 i4 o1 o2 o3 o4) 
              (not (and (=> o1 o2) (=> o2 o3) (=> o3 o4)) ) )) false))

(check-sat)