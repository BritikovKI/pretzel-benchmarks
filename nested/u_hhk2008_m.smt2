(set-logic HORN)
(declare-fun inv1 (Int Int Int Int Int) Bool)
(declare-fun inv2 (Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|count'| Int)) (=> (and (= |_FH_1'| |_FH_3'|) (<= 0 |_FH_1'|) (<= |_FH_1'| 100) (= |_FH_0'| |_FH_2'|) (<= |_FH_0'| 1000) (= |count'| 0)) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= |_FH_3'| (+ _FH_3 100)) (= |_FH_2'| (- _FH_2 100)) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (> _FH_3 0) (= |_FH_3'| (- _FH_3 1)) (= |_FH_2'| (+ _FH_2 1)) (inv2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= _FH_2 |_FH_2'|) (= _FH_3 |_FH_3'|) (inv2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (count Int)) (=> (and (<= _FH_3 0) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3) (= _FH_2 (+ _FH_0 _FH_1)) (> count 100)) false)))

(check-sat)
