(set-logic HORN)
(declare-fun INV0 (Int Int Int Int) Bool)
(declare-fun INV1 (Int Int Int Int) Bool)
(declare-fun INV2 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|count'| Int)) (=> (and (= 0 |_FH_1'|) (= 0 |_FH_2'|) (> |_FH_0'| 0) (= |count'| 0)) (INV0 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (> _FH_0 0) (= |_FH_0'| (- _FH_0 1)) (= _FH_1 |_FH_1'|) (INV0 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (INV1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_1'| (+ _FH_1 1)) (= |_FH_2'| (- _FH_2 1)) (< _FH_1 _FH_0) (= _FH_0 |_FH_0'|) (INV1 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (INV1 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (>= _FH_1 _FH_0) (INV1 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (INV2 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= |_FH_1'| (- _FH_1 1)) (= |_FH_2'| (+ _FH_2 1)) (< _FH_2 _FH_0) (INV2 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (INV2 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (>= _FH_2 _FH_0) (INV2 count _FH_0 _FH_1 _FH_2) (= |count'| (+ count 1))) (INV0 |count'| |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (count Int)) (=> (and (distinct _FH_1 _FH_2) (INV0 count _FH_0 _FH_1 _FH_2) (distinct _FH_0 0) (> count 100)) false)))

(check-sat)
