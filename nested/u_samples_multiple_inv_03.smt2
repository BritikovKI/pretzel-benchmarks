(set-logic HORN)
(declare-fun WRAP (Int Int) Bool)
(declare-fun NEST (Int Int) Bool)
(declare-fun WEEE (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 0) (= |count'| 0)) (WRAP |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (WRAP count _FH_0) (= |count'| (+ count 1))) (NEST |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (NEST count _FH_0) (= |count'| (+ count 1))) (WEEE |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (WEEE count _FH_0) (= |count'| (+ count 1))) (WEEE |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (WEEE count _FH_0) (= |count'| (+ count 1))) (NEST |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (NEST count _FH_0) (= |count'| (+ count 1))) (WRAP |count'| |_FH_0'|))))

(assert (forall ((_FH_0 Int) (count Int)) (=> (and (WRAP count _FH_0) (>= _FH_0 0) (> count 100)) false)))

(check-sat)
