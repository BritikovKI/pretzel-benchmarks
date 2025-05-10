(set-logic HORN)
(declare-fun inv (Int Int Int Int Int Int Int) Bool)
(declare-fun inv1 (Int Int Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|_FH_4'| Int) (|_FH_5'| Int) (|count'| Int)) (=> (and (= |_FH_0'| 1) (= |_FH_1'| 0) (= |_FH_1'| |_FH_3'|) (= |_FH_1'| |_FH_4'|) (= |_FH_1'| |_FH_5'|) (= |_FH_2'| (- |_FH_0'| |_FH_1'|)) (= |count'| 0)) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_4 |_FH_4'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (= _FH_5 |_FH_5'|) (= _FH_1 |_FH_1'|) (inv count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= |_FH_3'| (ite (= (mod |_FH_2'| 2) 1) (+ _FH_3 1) _FH_3)) (= |_FH_5'| (+ _FH_5 2)) (= |_FH_2'| (+ _FH_2 _FH_3 _FH_4 _FH_5)) (= |_FH_4'| (+ _FH_4 1)) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (= |count'| (+ count 1))) (inv1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_2 |_FH_2'|) (= _FH_4 |_FH_4'|) (= _FH_0 |_FH_0'|) (= _FH_3 |_FH_3'|) (= _FH_5 |_FH_5'|) (= _FH_1 |_FH_1'|) (inv1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (= |count'| (+ count 1))) (inv |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int)) (=> (and (inv count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (= _FH_3 _FH_4) (> count 100)) false)))

(check-sat)
