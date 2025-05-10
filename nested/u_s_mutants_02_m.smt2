(set-logic HORN)
(declare-fun itp1 (Int Int Int Int Int) Bool)
(declare-fun itp2 (Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 0) (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |count'| 0)) (itp1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_2'|) (= |_FH_0'| _FH_3) (= _FH_2 |_FH_3'|) (itp1 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (itp2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 |_FH_0'|)) (= |_FH_2'| (+ _FH_2 |_FH_1'|)) (= |_FH_3'| (+ _FH_3 |_FH_2'|)) (itp2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (itp2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_0 |_FH_3'|) (= |_FH_0'| _FH_1) (= |_FH_1'| _FH_3) (itp2 count _FH_0 _FH_1 _FH_2 _FH_3) (= |count'| (+ count 1))) (itp1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (count Int)) (=> (and (itp1 count _FH_0 _FH_1 _FH_2 _FH_3) (>= _FH_3 0) (> count 100)) false)))

(check-sat)
