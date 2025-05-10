(set-logic HORN)
(declare-fun inv1 (Int Int Int Int) Bool)
(declare-fun inv2 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|count'| Int)) (=> (and (= 0 |_FH_0'|) (= 0 |_FH_1'|) (= 0 |_FH_2'|) (= |count'| 0)) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (inv1 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (< _FH_0 100) (= |_FH_2'| (- _FH_1 1)) (= |_FH_1'| (+ _FH_2 1)) (= |_FH_0'| (+ _FH_0 _FH_1)) (inv2 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (inv2 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (count Int)) (=> (and (inv1 count _FH_0 _FH_1 _FH_2) (>= _FH_0 0) (> count 100)) false)))

(check-sat)
