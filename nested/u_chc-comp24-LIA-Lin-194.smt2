(set-logic HORN)
(declare-fun h1 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h2 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h3 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h4 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h5 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h6 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h7 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h36 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h8 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h9 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h10 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h14 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h15 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h16 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h19 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h17 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h18 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h20 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h21 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h22 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h23 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h24 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h25 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h26 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h35 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h27 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h28 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h29 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h30 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h31 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h32 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h33 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun h34 (Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|_FH_4'| Int) (|_FH_5'| Int) (|_FH_6'| Int) (|_FH_7'| Int) (|count'| Int)) (=> (and (= |_FH_3'| |_FH_7'|) (= |_FH_2'| |_FH_6'|) (= |_FH_1'| |_FH_5'|) (= |_FH_0'| |_FH_4'|) (= |count'| 0)) (h1 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h2 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (>= _FH_7 1) (h2 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h3 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= |_FH_5'| 1) (h3 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h4 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h4 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h5 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h5 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h6 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h6 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h7 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h36 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h7 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h7 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h8 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (<= (+ _FH_5 (* (- 1) _FH_6)) (- 1)) (h8 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h9 |count'|
    |_FH_0'|
    |_FH_1'|
    |_FH_2'|
    |_FH_3'|
    |_FH_4'|
    |_FH_5'|
    |_FH_6'|
    |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_2 |_FH_2'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= |_FH_4'| _FH_7) (= |_FH_4'| |_FH_7'|) (h9 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h10 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h10 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h14 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h14 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h15 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h15 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h16 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h19 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h16 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h16 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h17 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (<= (+ _FH_4 (* (- 1) _FH_6)) (- 1)) (h17 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h18 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= _FH_4 (+ (- 1) |_FH_4'|)) (h18 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h19 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (>= (+ _FH_4 (* (- 1) _FH_6)) 0) (h17 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h20 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h20 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h21 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h21 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h22 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_2 |_FH_2'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= |_FH_4'| _FH_7) (= |_FH_4'| |_FH_7'|) (h22 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h23 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h23 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h24 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h24 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h25 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h25 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h26 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h35 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h26 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h26 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h27 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (<= (+ _FH_4 (* (- 1) _FH_6)) (- 1)) (h27 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h28 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h28 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h29 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (>= (+ _FH_4 (* (- 1) _FH_6)) 0) (h27 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h30 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h30 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h31 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (h31 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h32 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (<= _FH_5 0) (h29 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h33 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (>= _FH_5 1) (h29 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h34 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_5 |_FH_5'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= _FH_4 (+ (- 1) |_FH_4'|)) (h34 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h35 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (_FH_6 Int) (|_FH_6'| Int) (_FH_7 Int) (|_FH_7'| Int) (count Int) (|count'| Int)) (=> (and (= _FH_0 |_FH_0'|) (= _FH_1 |_FH_1'|) (= _FH_4 |_FH_4'|) (= _FH_2 |_FH_2'|) (= _FH_7 |_FH_7'|) (= _FH_3 |_FH_3'|) (= _FH_6 |_FH_6'|) (= _FH_5 (+ (- 1) |_FH_5'|)) (h32 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (= |count'| (+ count 1))) (h36 |count'|
     |_FH_0'|
     |_FH_1'|
     |_FH_2'|
     |_FH_3'|
     |_FH_4'|
     |_FH_5'|
     |_FH_6'|
     |_FH_7'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (_FH_6 Int) (_FH_7 Int) (count Int)) (=> (and (h33 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (> count 100)) false)))

(check-sat)
