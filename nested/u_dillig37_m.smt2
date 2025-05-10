(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(declare-fun inv1 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|count'| Int)) (=> (and (> |_FH_2'| 0) (= |_FH_0'| 0) (= |_FH_0'| |_FH_1'|) (= |count'| 0)) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_2'| (- _FH_2 1)) (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (inv count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (< _FH_0 _FH_2) (= _FH_2 |_FH_2'|) (or (= |_FH_1'| _FH_0) (= |_FH_1'| _FH_1)) (inv1 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= |_FH_2'| (+ _FH_2 1)) (inv1 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (count Int)) (=> (and (>= _FH_0 _FH_2) (inv count _FH_0 _FH_1 _FH_2) (<= 0 _FH_1) (<= _FH_1 _FH_2) (> count 100)) false)))

(check-sat)
