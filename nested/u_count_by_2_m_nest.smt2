(set-logic HORN)
(declare-fun itp1 (Int Int) Bool)
(declare-fun itp2 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|count'| Int)) (=> (and (= 0 |_FH_0'|) (= |count'| 0)) (itp1 |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= 0 |_FH_1'|) (< _FH_0 256) (= _FH_0 |_FH_0'|) (itp1 count _FH_0) (= |count'| (+ count 1))) (itp2 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (< _FH_1 16) (= |_FH_1'| (+ _FH_1 2)) (itp2 count _FH_0 _FH_1) (= |count'| (+ count 1))) (itp2 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (count Int) (|count'| Int)) (=> (and (>= _FH_1 16) (= |_FH_0'| (+ _FH_0 _FH_1)) (itp2 count _FH_0 _FH_1) (= |count'| (+ count 1))) (itp1 |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (count Int)) (=> (and (< _FH_0 256) (distinct _FH_0 256) (itp1 count _FH_0) (> count 100)) false)))

(check-sat)
