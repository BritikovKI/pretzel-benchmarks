(set-logic HORN)
(declare-fun verifier.error (Bool Bool Bool) Bool)
(declare-fun main@entry () Bool)
(declare-fun main@.lr.ph9 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun main@_31 (Int Bool Bool Int Int) Bool)
(declare-fun main@verifier.error.split () Bool)
(declare-fun main@.lr.ph6 (Int Int Int Int Int Int Int Int) Bool)
(assert (=> true (verifier.error false false false)))
(assert (=> true (verifier.error false true true)))
(assert (=> true (verifier.error true false true)))
(assert (=> true (verifier.error true true true)))
(assert (=> true main@entry))
(assert (forall ((main@%_7_0 Int)
         (main@%.04.i7_1 Int)
         (main@%_6_0 Int)
         (main@%.03.i8_1 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@.lr.ph9_0 Bool)
         (main@%.04.i7_0 Int)
         (main@entry_0 Bool)
         (main@%.03.i8_0 Int)
         (main@%_13_0 Bool)
         (main@%_12_0 Bool)
         (main@%_10_0 Bool)
         (main@%_11_0 Bool)
         (main@%_8_0 Int)
         (main@%_9_0 Int)
         (main@%_0_0 Bool))
  (=> (and main@entry
           (= main@%_0_0 (= main@%loop.bound_0 1))
           main@%_0_0
           (= main@%_10_0 (> main@%_9_0 49))
           (= main@%_11_0 (< main@%_8_0 501))
           (= main@%_12_0 (and main@%_11_0 main@%_10_0))
           main@%_12_0
           (= main@%_13_0 (> main@%_7_0 0))
           (=> main@.lr.ph9_0 (and main@.lr.ph9_0 main@entry_0))
           (=> (and main@.lr.ph9_0 main@entry_0) main@%_13_0)
           (=> (and main@.lr.ph9_0 main@entry_0) (= main@%.03.i8_0 0))
           (=> (and main@.lr.ph9_0 main@entry_0) (= main@%.04.i7_0 0))
           (=> (and main@.lr.ph9_0 main@entry_0)
               (= main@%.03.i8_1 main@%.03.i8_0))
           (=> (and main@.lr.ph9_0 main@entry_0)
               (= main@%.04.i7_1 main@%.04.i7_0))
           main@.lr.ph9_0)
      (main@.lr.ph9 main@%_5_0
                    main@%_4_0
                    main@%_3_0
                    main@%_2_0
                    main@%_1_0
                    main@%loop.bound_0
                    main@%.03.i8_1
                    main@%_6_0
                    main@%.04.i7_1
                    main@%_7_0))))
(assert (forall ((main@%_5_0 Int)
         (main@%.0.i2_1 Int)
         (main@%_28_0 Bool)
         (main@%_25_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@_31_0 Bool)
         (main@%.0.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_23_0 Bool)
         (main@%_24_0 Bool)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.05.i.lcssa_0 Int)
         (main@entry_0 Bool)
         (main@%_13_0 Bool)
         (main@%_7_0 Int)
         (main@%_12_0 Bool)
         (main@%_10_0 Bool)
         (main@%_11_0 Bool)
         (main@%_8_0 Int)
         (main@%_9_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_23_0 (> main@%_4_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_2_0 (- 1))))))
  (let ((a!3 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_10_0 (> main@%_9_0 49))
                  (= main@%_11_0 (< main@%_8_0 501))
                  (= main@%_12_0 (and main@%_11_0 main@%_10_0))
                  main@%_12_0
                  (= main@%_13_0 (> main@%_7_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_13_0))
                  (=> (and main@.preheader_0 main@entry_0)
                      (= main@%.05.i.lcssa_0 0))
                  (=> (and main@.preheader_0 main@entry_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_22_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_24_0 (< main@%_3_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_25_0 (and main@%_24_0 main@%_23_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_1_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  (=> main@_31_0 (and main@_31_0 main@.lr.ph_0))
                  (=> (and main@_31_0 main@.lr.ph_0) (= main@%.0.i2_0 0))
                  (=> (and main@_31_0 main@.lr.ph_0)
                      (= main@%.0.i2_1 main@%.0.i2_0))
                  main@_31_0)))
    (=> a!3
        (main@_31 main@%.05.i.lcssa_1
                  main@%_25_0
                  main@%_28_0
                  main@%.0.i2_1
                  main@%_5_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%_34_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_5_0 Int)
         (main@%.05.i.lcssa_0 Int)
         (main@entry_0 Bool)
         (main@%_13_0 Bool)
         (main@%_7_0 Int)
         (main@%_12_0 Bool)
         (main@%_10_0 Bool)
         (main@%_11_0 Bool)
         (main@%_8_0 Int)
         (main@%_9_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_10_0 (> main@%_9_0 49))
                  (= main@%_11_0 (< main@%_8_0 501))
                  (= main@%_12_0 (and main@%_11_0 main@%_10_0))
                  main@%_12_0
                  (= main@%_13_0 (> main@%_7_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_13_0))
                  (=> (and main@.preheader_0 main@entry_0)
                      (= main@%.05.i.lcssa_0 0))
                  (=> (and main@.preheader_0 main@entry_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_22_0))
                  (=> main@verifier.error_0
                      (= main@%_34_0 (< main@%.05.i.lcssa_1 300)))
                  (=> main@verifier.error_0 (not main@%_34_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!1 main@verifier.error.split))))
(assert (forall ((main@%_7_0 Int)
         (main@%.04.i7_2 Int)
         (main@%_6_0 Int)
         (main@%.03.i8_2 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@.lr.ph9_1 Bool)
         (main@%.04.i7_1 Int)
         (main@.lr.ph9_0 Bool)
         (main@%.03.i8_1 Int)
         (main@%_15_0 Int)
         (main@%_14_0 Int)
         (main@%_16_0 Bool)
         (main@%.04.i7_0 Int)
         (main@%.03.i8_0 Int))
  (=> (and (main@.lr.ph9 main@%_5_0
                         main@%_4_0
                         main@%_3_0
                         main@%_2_0
                         main@%_1_0
                         main@%loop.bound_0
                         main@%.03.i8_0
                         main@%_6_0
                         main@%.04.i7_0
                         main@%_7_0)
           (= main@%_14_0 (+ main@%.03.i8_0 1))
           (= main@%_15_0 (+ main@%.04.i7_0 1))
           (= main@%_16_0 (< main@%_15_0 main@%_7_0))
           (=> main@.lr.ph9_1 (and main@.lr.ph9_1 main@.lr.ph9_0))
           (=> (and main@.lr.ph9_1 main@.lr.ph9_0) main@%_16_0)
           (=> (and main@.lr.ph9_1 main@.lr.ph9_0)
               (= main@%.03.i8_1 main@%_14_0))
           (=> (and main@.lr.ph9_1 main@.lr.ph9_0)
               (= main@%.04.i7_1 main@%_15_0))
           (=> (and main@.lr.ph9_1 main@.lr.ph9_0)
               (= main@%.03.i8_2 main@%.03.i8_1))
           (=> (and main@.lr.ph9_1 main@.lr.ph9_0)
               (= main@%.04.i7_2 main@%.04.i7_1))
           main@.lr.ph9_1)
      (main@.lr.ph9 main@%_5_0
                    main@%_4_0
                    main@%_3_0
                    main@%_2_0
                    main@%_1_0
                    main@%loop.bound_0
                    main@%.03.i8_2
                    main@%_6_0
                    main@%.04.i7_2
                    main@%_7_0))))
(assert (forall ((main@%loop.bound_0 Int)
         (main@%.1.i5_1 Int)
         (main@%.05.i4_1 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@.lr.ph6_0 Bool)
         (main@%.05.i4_0 Int)
         (main@_20_0 Bool)
         (main@%.1.i5_0 Int)
         (main@%.03.i8_0 Int)
         (main@%_21_0 Bool)
         (main@%_18_0 Bool)
         (|tuple(main@.lr.ph6.peel_0, main@_20_0)| Bool)
         (main@_19_0 Bool)
         (main@.lr.ph6.peel_0 Bool)
         (main@%_6_0 Int)
         (main@%_17_0 Bool)
         (main@%_16_0 Bool)
         (main@.lr.ph9_0 Bool)
         (main@%_7_0 Int)
         (main@%_15_0 Int)
         (main@%.04.i7_0 Int)
         (main@%_14_0 Int))
  (let ((a!1 (=> main@.lr.ph6.peel_0
                 (= main@%_17_0 (ite (>= main@%_6_0 0) (< main@%_6_0 2) false)))))
  (let ((a!2 (and (main@.lr.ph9 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%loop.bound_0
                                main@%.03.i8_0
                                main@%_6_0
                                main@%.04.i7_0
                                main@%_7_0)
                  (= main@%_14_0 (+ main@%.03.i8_0 1))
                  (= main@%_15_0 (+ main@%.04.i7_0 1))
                  (= main@%_16_0 (< main@%_15_0 main@%_7_0))
                  (=> main@.lr.ph6.peel_0
                      (and main@.lr.ph6.peel_0 main@.lr.ph9_0))
                  (=> (and main@.lr.ph6.peel_0 main@.lr.ph9_0)
                      (not main@%_16_0))
                  a!1
                  (=> main@.lr.ph6.peel_0 main@%_17_0)
                  (=> main@.lr.ph6.peel_0 (= main@%_18_0 (= main@%_6_0 1)))
                  (=> main@_19_0 (and main@_19_0 main@.lr.ph6.peel_0))
                  (=> (and main@_19_0 main@.lr.ph6.peel_0) (not main@%_18_0))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)|
                      main@.lr.ph6.peel_0)
                  (=> main@_20_0
                      (or (and main@_20_0 main@_19_0)
                          |tuple(main@.lr.ph6.peel_0, main@_20_0)|))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)| main@%_18_0)
                  (=> main@_20_0 (= main@%_21_0 (= main@%.03.i8_0 0)))
                  (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@_20_0))
                  (=> (and main@.lr.ph6_0 main@_20_0) (not main@%_21_0))
                  (=> (and main@.lr.ph6_0 main@_20_0)
                      (= main@%.1.i5_0 main@%.03.i8_0))
                  (=> (and main@.lr.ph6_0 main@_20_0) (= main@%.05.i4_0 1))
                  (=> (and main@.lr.ph6_0 main@_20_0)
                      (= main@%.1.i5_1 main@%.1.i5_0))
                  (=> (and main@.lr.ph6_0 main@_20_0)
                      (= main@%.05.i4_1 main@%.05.i4_0))
                  main@.lr.ph6_0)))
    (=> a!2
        (main@.lr.ph6 main@%_5_0
                      main@%_4_0
                      main@%_3_0
                      main@%_2_0
                      main@%_1_0
                      main@%.05.i4_1
                      main@%.1.i5_1
                      main@%loop.bound_0))))))
(assert (forall ((main@%_5_0 Int)
         (main@%.0.i2_1 Int)
         (main@%_28_0 Bool)
         (main@%_25_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@_31_0 Bool)
         (main@%.0.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_23_0 Bool)
         (main@%_24_0 Bool)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.05.i.lcssa_0 Int)
         (main@_20_0 Bool)
         (main@%_21_0 Bool)
         (main@%.03.i8_0 Int)
         (main@%_18_0 Bool)
         (|tuple(main@.lr.ph6.peel_0, main@_20_0)| Bool)
         (main@_19_0 Bool)
         (main@.lr.ph6.peel_0 Bool)
         (main@%_6_0 Int)
         (main@%_17_0 Bool)
         (main@%_16_0 Bool)
         (main@.lr.ph9_0 Bool)
         (main@%_7_0 Int)
         (main@%_15_0 Int)
         (main@%.04.i7_0 Int)
         (main@%_14_0 Int)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph6.peel_0
                 (= main@%_17_0 (ite (>= main@%_6_0 0) (< main@%_6_0 2) false))))
        (a!2 (=> main@.lr.ph_0 (= main@%_23_0 (> main@%_4_0 (- 1)))))
        (a!3 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_2_0 (- 1))))))
  (let ((a!4 (and (main@.lr.ph9 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%loop.bound_0
                                main@%.03.i8_0
                                main@%_6_0
                                main@%.04.i7_0
                                main@%_7_0)
                  (= main@%_14_0 (+ main@%.03.i8_0 1))
                  (= main@%_15_0 (+ main@%.04.i7_0 1))
                  (= main@%_16_0 (< main@%_15_0 main@%_7_0))
                  (=> main@.lr.ph6.peel_0
                      (and main@.lr.ph6.peel_0 main@.lr.ph9_0))
                  (=> (and main@.lr.ph6.peel_0 main@.lr.ph9_0)
                      (not main@%_16_0))
                  a!1
                  (=> main@.lr.ph6.peel_0 main@%_17_0)
                  (=> main@.lr.ph6.peel_0 (= main@%_18_0 (= main@%_6_0 1)))
                  (=> main@_19_0 (and main@_19_0 main@.lr.ph6.peel_0))
                  (=> (and main@_19_0 main@.lr.ph6.peel_0) (not main@%_18_0))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)|
                      main@.lr.ph6.peel_0)
                  (=> main@_20_0
                      (or (and main@_20_0 main@_19_0)
                          |tuple(main@.lr.ph6.peel_0, main@_20_0)|))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)| main@%_18_0)
                  (=> main@_20_0 (= main@%_21_0 (= main@%.03.i8_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_20_0))
                  (=> (and main@.preheader_0 main@_20_0) main@%_21_0)
                  (=> (and main@.preheader_0 main@_20_0)
                      (= main@%.05.i.lcssa_0 1))
                  (=> (and main@.preheader_0 main@_20_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_22_0)
                  a!2
                  (=> main@.lr.ph_0 (= main@%_24_0 (< main@%_3_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_25_0 (and main@%_24_0 main@%_23_0)))
                  a!3
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_1_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  (=> main@_31_0 (and main@_31_0 main@.lr.ph_0))
                  (=> (and main@_31_0 main@.lr.ph_0) (= main@%.0.i2_0 0))
                  (=> (and main@_31_0 main@.lr.ph_0)
                      (= main@%.0.i2_1 main@%.0.i2_0))
                  main@_31_0)))
    (=> a!4
        (main@_31 main@%.05.i.lcssa_1
                  main@%_25_0
                  main@%_28_0
                  main@%.0.i2_1
                  main@%_5_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%_34_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_5_0 Int)
         (main@%.05.i.lcssa_0 Int)
         (main@_20_0 Bool)
         (main@%_21_0 Bool)
         (main@%.03.i8_0 Int)
         (main@%_18_0 Bool)
         (|tuple(main@.lr.ph6.peel_0, main@_20_0)| Bool)
         (main@_19_0 Bool)
         (main@.lr.ph6.peel_0 Bool)
         (main@%_6_0 Int)
         (main@%_17_0 Bool)
         (main@%_16_0 Bool)
         (main@.lr.ph9_0 Bool)
         (main@%_7_0 Int)
         (main@%_15_0 Int)
         (main@%.04.i7_0 Int)
         (main@%_14_0 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int))
  (let ((a!1 (=> main@.lr.ph6.peel_0
                 (= main@%_17_0 (ite (>= main@%_6_0 0) (< main@%_6_0 2) false)))))
  (let ((a!2 (and (main@.lr.ph9 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%loop.bound_0
                                main@%.03.i8_0
                                main@%_6_0
                                main@%.04.i7_0
                                main@%_7_0)
                  (= main@%_14_0 (+ main@%.03.i8_0 1))
                  (= main@%_15_0 (+ main@%.04.i7_0 1))
                  (= main@%_16_0 (< main@%_15_0 main@%_7_0))
                  (=> main@.lr.ph6.peel_0
                      (and main@.lr.ph6.peel_0 main@.lr.ph9_0))
                  (=> (and main@.lr.ph6.peel_0 main@.lr.ph9_0)
                      (not main@%_16_0))
                  a!1
                  (=> main@.lr.ph6.peel_0 main@%_17_0)
                  (=> main@.lr.ph6.peel_0 (= main@%_18_0 (= main@%_6_0 1)))
                  (=> main@_19_0 (and main@_19_0 main@.lr.ph6.peel_0))
                  (=> (and main@_19_0 main@.lr.ph6.peel_0) (not main@%_18_0))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)|
                      main@.lr.ph6.peel_0)
                  (=> main@_20_0
                      (or (and main@_20_0 main@_19_0)
                          |tuple(main@.lr.ph6.peel_0, main@_20_0)|))
                  (=> |tuple(main@.lr.ph6.peel_0, main@_20_0)| main@%_18_0)
                  (=> main@_20_0 (= main@%_21_0 (= main@%.03.i8_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_20_0))
                  (=> (and main@.preheader_0 main@_20_0) main@%_21_0)
                  (=> (and main@.preheader_0 main@_20_0)
                      (= main@%.05.i.lcssa_0 1))
                  (=> (and main@.preheader_0 main@_20_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_22_0))
                  (=> main@verifier.error_0
                      (= main@%_34_0 (< main@%.05.i.lcssa_1 300)))
                  (=> main@verifier.error_0 (not main@%_34_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!2 main@verifier.error.split)))))
(assert (forall ((main@%loop.bound_0 Int)
         (main@%.1.i5_2 Int)
         (main@%.05.i4_2 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@.lr.ph6_1 Bool)
         (main@%.05.i4_1 Int)
         (main@.lr.ph6_0 Bool)
         (main@%.1.i5_1 Int)
         (main@%_29_0 Int)
         (main@%.7.i_0 Int)
         (main@%_30_0 Bool)
         (main@%.1.i5_0 Int)
         (main@%.05.i4_0 Int))
  (let ((a!1 (and (main@.lr.ph6 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%.05.i4_0
                                main@%.1.i5_0
                                main@%loop.bound_0)
                  (= main@%_29_0 (+ main@%.05.i4_0 1))
                  (= main@%.7.i_0 (+ main@%.1.i5_0 (- 1)))
                  (= main@%_30_0 (> main@%.1.i5_0 main@%loop.bound_0))
                  (=> main@.lr.ph6_1 (and main@.lr.ph6_1 main@.lr.ph6_0))
                  (=> (and main@.lr.ph6_1 main@.lr.ph6_0) main@%_30_0)
                  (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
                      (= main@%.1.i5_1 main@%.7.i_0))
                  (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
                      (= main@%.05.i4_1 main@%_29_0))
                  (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
                      (= main@%.1.i5_2 main@%.1.i5_1))
                  (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
                      (= main@%.05.i4_2 main@%.05.i4_1))
                  main@.lr.ph6_1)))
    (=> a!1
        (main@.lr.ph6 main@%_5_0
                      main@%_4_0
                      main@%_3_0
                      main@%_2_0
                      main@%_1_0
                      main@%.05.i4_2
                      main@%.1.i5_2
                      main@%loop.bound_0)))))
(assert (forall ((main@%_5_0 Int)
         (main@%.0.i2_1 Int)
         (main@%_28_0 Bool)
         (main@%_25_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@_31_0 Bool)
         (main@%.0.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_23_0 Bool)
         (main@%_24_0 Bool)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.05.i.lcssa_0 Int)
         (main@.lr.ph6_0 Bool)
         (main@%_29_0 Int)
         (main@%_30_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.1.i5_0 Int)
         (main@%.7.i_0 Int)
         (main@%.05.i4_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_23_0 (> main@%_4_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_2_0 (- 1))))))
  (let ((a!3 (and (main@.lr.ph6 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%.05.i4_0
                                main@%.1.i5_0
                                main@%loop.bound_0)
                  (= main@%_29_0 (+ main@%.05.i4_0 1))
                  (= main@%.7.i_0 (+ main@%.1.i5_0 (- 1)))
                  (= main@%_30_0 (> main@%.1.i5_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_30_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0)
                      (= main@%.05.i.lcssa_0 main@%_29_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_22_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_24_0 (< main@%_3_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_25_0 (and main@%_24_0 main@%_23_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_1_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  (=> main@_31_0 (and main@_31_0 main@.lr.ph_0))
                  (=> (and main@_31_0 main@.lr.ph_0) (= main@%.0.i2_0 0))
                  (=> (and main@_31_0 main@.lr.ph_0)
                      (= main@%.0.i2_1 main@%.0.i2_0))
                  main@_31_0)))
    (=> a!3
        (main@_31 main@%.05.i.lcssa_1
                  main@%_25_0
                  main@%_28_0
                  main@%.0.i2_1
                  main@%_5_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%_34_0 Bool)
         (main@%.05.i.lcssa_1 Int)
         (main@%_22_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_5_0 Int)
         (main@%.05.i.lcssa_0 Int)
         (main@.lr.ph6_0 Bool)
         (main@%_29_0 Int)
         (main@%_30_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.1.i5_0 Int)
         (main@%.7.i_0 Int)
         (main@%.05.i4_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int))
  (let ((a!1 (and (main@.lr.ph6 main@%_5_0
                                main@%_4_0
                                main@%_3_0
                                main@%_2_0
                                main@%_1_0
                                main@%.05.i4_0
                                main@%.1.i5_0
                                main@%loop.bound_0)
                  (= main@%_29_0 (+ main@%.05.i4_0 1))
                  (= main@%.7.i_0 (+ main@%.1.i5_0 (- 1)))
                  (= main@%_30_0 (> main@%.1.i5_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_30_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0)
                      (= main@%.05.i.lcssa_0 main@%_29_0))
                  (=> (and main@.preheader_0 main@.lr.ph6_0)
                      (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                  (=> main@.preheader_0 (= main@%_22_0 (> main@%_5_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_22_0))
                  (=> main@verifier.error_0
                      (= main@%_34_0 (< main@%.05.i.lcssa_1 300)))
                  (=> main@verifier.error_0 (not main@%_34_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!1 main@verifier.error.split))))
(assert (forall ((main@%_5_0 Int)
         (main@%.0.i2_2 Int)
         (main@%_28_0 Bool)
         (main@%_25_0 Bool)
         (main@%.05.i.lcssa_0 Int)
         (main@_31_1 Bool)
         (main@%.0.i2_1 Int)
         (main@_31_0 Bool)
         (main@%_32_0 Int)
         (main@%_33_0 Bool)
         (main@%.0.i2_0 Int))
  (=> (and (main@_31 main@%.05.i.lcssa_0
                     main@%_25_0
                     main@%_28_0
                     main@%.0.i2_0
                     main@%_5_0)
           main@%_25_0
           main@%_28_0
           (= main@%_32_0 (+ main@%.0.i2_0 1))
           (= main@%_33_0 (< main@%_32_0 main@%_5_0))
           (=> main@_31_1 (and main@_31_1 main@_31_0))
           (=> (and main@_31_1 main@_31_0) main@%_33_0)
           (=> (and main@_31_1 main@_31_0) (= main@%.0.i2_1 main@%_32_0))
           (=> (and main@_31_1 main@_31_0) (= main@%.0.i2_2 main@%.0.i2_1))
           main@_31_1)
      (main@_31 main@%.05.i.lcssa_0
                main@%_25_0
                main@%_28_0
                main@%.0.i2_2
                main@%_5_0))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%_34_0 Bool)
         (main@%.05.i.lcssa_0 Int)
         (main@%_33_0 Bool)
         (main@_31_0 Bool)
         (main@%_5_0 Int)
         (main@%_32_0 Int)
         (main@%.0.i2_0 Int)
         (main@%_28_0 Bool)
         (main@%_25_0 Bool))
  (let ((a!1 (and (main@_31 main@%.05.i.lcssa_0
                            main@%_25_0
                            main@%_28_0
                            main@%.0.i2_0
                            main@%_5_0)
                  main@%_25_0
                  main@%_28_0
                  (= main@%_32_0 (+ main@%.0.i2_0 1))
                  (= main@%_33_0 (< main@%_32_0 main@%_5_0))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@_31_0))
                  (=> (and main@verifier.error_0 main@_31_0) (not main@%_33_0))
                  (=> main@verifier.error_0
                      (= main@%_34_0 (< main@%.05.i.lcssa_0 300)))
                  (=> main@verifier.error_0 (not main@%_34_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!1 main@verifier.error.split))))
(assert (=> main@verifier.error.split false))
(check-sat)
