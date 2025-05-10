(set-logic HORN)
(declare-fun LOOPX (Int Int) Bool)
(declare-fun LOOPY (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 3138) (= |count'| 0)) (LOOPX |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= |_FH_1'| 0) (LOOPX count _FH_0) (= |count'| (+ count 1))) (LOOPY |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (or (distinct (mod _FH_1 3) 0) (<= _FH_1 0)) (= |_FH_1'| (+ _FH_1 2)) (LOOPY count _FH_0 _FH_1) (= |count'| (+ count 1))) (LOOPY |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (count Int) (|count'| Int)) (=> (and (= (mod _FH_1 3) 0) (> _FH_1 0) (= |_FH_0'| (+ _FH_0 _FH_1)) (LOOPY count _FH_0 _FH_1) (= |count'| (+ count 1))) (LOOPX |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (count Int)) (=> (and (LOOPX count _FH_0) (= (mod _FH_0 6) 0) (> count 100)) false)))

(check-sat)
