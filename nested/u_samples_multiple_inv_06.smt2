(set-logic HORN)
(declare-fun I (Int Int) Bool)
(declare-fun J (Int Int Int) Bool)
(declare-fun K (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 0) (= |count'| 0)) (I |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= |_FH_1'| 0) (I count _FH_0) (= |count'| (+ count 1))) (J |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= |_FH_1'| (+ _FH_1 1)) (J count _FH_0 _FH_1) (= |count'| (+ count 1))) (J |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 _FH_1)) (J count _FH_0 _FH_1) (= |count'| (+ count 1))) (I |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (- _FH_0)) (I count _FH_0) (= |count'| (+ count 1))) (K |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (- _FH_0 1)) (K count _FH_0) (= |count'| (+ count 1))) (K |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (count Int)) (=> (and (K count _FH_0) (<= _FH_0 0) (> count 100)) false)))

(check-sat)
