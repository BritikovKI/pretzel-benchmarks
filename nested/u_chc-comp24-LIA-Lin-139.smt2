(set-logic HORN)
(declare-fun f$unknown:2 (Int Int Int) Bool)
(declare-fun f$unknown:4 (Int Int Int) Bool)
(declare-fun incr$unknown:6 (Int Int Int) Bool)

(assert (forall ((C Int) (D Int) (_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= (= 0 D) (<= (- 3) C)) (distinct 0 D) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (|f$unknown:2| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:2| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((F Int) (_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= (= 0 0) (<= (- 3) (+ F 2))) (distinct (= 0 0) (<= (+ F 2) 1)) (|f$unknown:2| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:2| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((F Int) (_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= (= 0 0) (<= (- 3) (+ F 2))) (distinct (= 0 0) (<= (+ F 2) 1)) (|f$unknown:4| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:2| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (|incr$unknown:6| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:2| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((D Int) (_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (distinct 0 D) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (distinct (= 0 D) (<= _FH_1 1)) (= (= 0 0) (<= (- 3) _FH_1)) (|f$unknown:2| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:4| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((C Int) (_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (distinct 0 C) (= _FH_1 (- 4)) (= (= 0 C) (<= (- 3) |_FH_1'|)) (|f$unknown:4| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:4| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 (+ (- 2) |_FH_1'|)) (= (= 0 0) (<= (- 3) |_FH_1'|)) (distinct (= 0 0) (<= |_FH_1'| 1)) (|f$unknown:4| count _FH_0 _FH_1) (= |count'| (+ count 1))) (|f$unknown:4| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|count'| Int)) (=> (and (= |_FH_0'| (+ 1 |_FH_1'|)) (= |count'| 0)) (|incr$unknown:6| |count'| |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (count Int)) (=> (and (distinct (= 0 0) (>= _FH_0 (- 3))) (|f$unknown:4| count _FH_0 _FH_1) (distinct _FH_1 3) (> count 100)) false)))

(check-sat)
