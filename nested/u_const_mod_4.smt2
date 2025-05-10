(set-logic HORN)
(declare-fun inv1 (Int Int Int) Bool)
(declare-fun inv3 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|count'| Int)) (=> (and (= |_FH_0'| (* |_FH_1'| 3)) (= |count'| 0)) (inv1 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (= _FH_1 |_FH_1'|) (inv1 count _FH_0 _FH_1) (= |count'| (+ count 1))) (inv3 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 3)) (= |_FH_1'| (+ _FH_1 1)) (inv3 count _FH_0 _FH_1) (= |count'| (+ count 1))) (inv3 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (+ _FH_0 2)) (inv3 count _FH_0 _FH_1) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (count Int)) (=> (and (inv1 count _FH_0 _FH_1) (= (mod _FH_0 3) 0) (> count 100)) false)))

(check-sat)
