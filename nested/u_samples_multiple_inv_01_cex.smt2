(set-logic HORN)
(declare-fun WRAP (Int Int) Bool)
(declare-fun NEST (Int Int) Bool)
(declare-fun fail (Int ) Bool)

(assert (forall ((|_FH_0'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 0) (= |count'| 0)) (WRAP |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (WRAP count _FH_0) (= |count'| (+ count 1))) (NEST |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (NEST count _FH_0) (= |count'| (+ count 1))) (NEST |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (NEST count _FH_0) (= |count'| (+ count 1))) (WRAP |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (count Int) (|count'| Int)) (=> (and (>= _FH_0 15) (WRAP count _FH_0) (= |count'| (+ count 1))) (fail |count'|))))

(assert (forall ((fail Bool) (|count'| Int)) (=> (and fail (= |count'| 0)) false)))

(check-sat)
