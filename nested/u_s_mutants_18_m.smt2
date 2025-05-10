(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)
(declare-fun inv1 (Int Int Int Int Int) Bool)
(declare-fun inv2 (Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 0) (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_3'| 1) (= |count'| 0)) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (inv count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (ite (= _FH_0 0) 1 0)) (= |_FH_2'| (ite (= _FH_0 0) (+ _FH_2 1) _FH_2)) (= |_FH_1'| (ite (= _FH_3 1) (+ _FH_1 1) _FH_1)) (= |_FH_3'| (ite (= _FH_3 1) 0 1)) (inv2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (inv2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (count Int)) (=> (and (inv count _FH_0 _FH_1 _FH_2 _FH_3) (= _FH_1 _FH_2) (> count 100)) false)))

(check-sat)
