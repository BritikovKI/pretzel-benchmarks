(set-logic HORN)
(declare-fun I (Int) Bool)
(declare-fun J (Int Int) Bool)
(declare-fun K (Int) Bool)
(declare-fun fail () Bool)
(assert (forall ((x Int)) (=> (= x 0) (I x))))
(assert (forall ((x Int) (x1 Int) (y1 Int))
  (=> (and (I x) (= x1 x) (= y1 0)) (J x1 y1))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (J x y) (= x1 x) (= y1 (+ y 1))) (J x1 y1))))
(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (J x y) (= x1 (+ x y))) (I x1))))
(assert (forall ((x Int) (z1 Int)) (=> (and (I x) (= z1 (- x))) (K z1))))
(assert (forall ((z Int) (z1 Int)) (=> (and (K z) (= z1 (- z 1))) (K z1))))
(assert (forall ((z Int)) (=> (and (K z) (not (<= z 0))) fail)))
(assert (=> fail false))
(check-sat)
