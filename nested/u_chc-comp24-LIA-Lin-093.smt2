(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(declare-fun itp (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 1) (= |_FH_0'| |_FH_1'|) (= |count'| 0)) (inv |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (+ 1 _FH_0)) (inv count _FH_0 _FH_1) (= |count'| (+ count 1))) (itp |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_1'| (+ _FH_1 |_FH_0'|)) (or (= |_FH_0'| (+ 1 _FH_0)) (= |_FH_0'| _FH_0)) (itp count _FH_0 _FH_1) (= |count'| (+ count 1))) (itp |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (itp count _FH_0 _FH_1) (= |count'| (+ count 1))) (inv |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (count Int)) (=> (and (inv count _FH_0 _FH_1) (>= _FH_1 1) (> count 100)) false)))

(check-sat)
