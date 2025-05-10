(set-logic HORN)
(declare-fun verifier.error (Bool Bool Bool) Bool)
(declare-fun main@entry () Bool)
(declare-fun main@.lr.ph6.split.split.split (Int Int Int Int Int Bool) Bool)
(declare-fun main@.lr.ph6.split.us () Bool)
(declare-fun main@.preheader.split () Bool)
(declare-fun main@.lr.ph (Int Int Int Int Int Int Int Bool) Bool)
(assert (=> true (verifier.error false false false)))
(assert (=> true (verifier.error false true true)))
(assert (=> true (verifier.error true false true)))
(assert (=> true (verifier.error true true true)))
(assert (=> true main@entry))
(assert (forall ((main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%_11_0 Int)
         (main@%loop.bound_0 Int)
         (main@%.0.i5_1 Int)
         (main@%.01.i3_1 Int)
         (main@.lr.ph6.split.split.split_0 Bool)
         (main@%.01.i3_0 Int)
         (main@.lr.ph6.split_0 Bool)
         (main@%.0.i5_0 Int)
         (main@%_6_0 Int)
         (main@%brmerge_0 Bool)
         (main@%_12_0 Bool)
         (main@%_13_0 Bool)
         (main@%_4_0 Int)
         (main@%_3_0 Int)
         (main@%_8_0 Bool)
         (main@.lr.ph6_0 Bool)
         (main@%_10_0 Bool)
         (main@%_1_0 Int)
         (main@%_5_0 Int)
         (main@%_7_0 Bool)
         (main@entry_0 Bool)
         (main@%_0_0 Bool))
  (let ((a!1 (=> main@.lr.ph6_0 (= main@%_10_0 (not (= main@%_1_0 1))))))
  (let ((a!2 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 0))
                  main@%_0_0
                  (= main@%_7_0 (= main@%_6_0 0))
                  (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
                  (=> (and main@.lr.ph6_0 main@entry_0) (not main@%_7_0))
                  (=> main@.lr.ph6_0 (= main@%_8_0 (= main@%_5_0 1)))
                  (=> main@.lr.ph6_0 (= main@%_9_0 (= main@%_2_0 0)))
                  a!1
                  (=> main@.lr.ph6_0 (= main@%_11_0 (ite main@%_10_0 1 0)))
                  (=> main@.lr.ph6.split_0
                      (and main@.lr.ph6.split_0 main@.lr.ph6_0))
                  (=> (and main@.lr.ph6.split_0 main@.lr.ph6_0)
                      (not main@%_8_0))
                  (=> main@.lr.ph6.split_0 (= main@%_12_0 (= main@%_3_0 0)))
                  (=> main@.lr.ph6.split_0 (= main@%_13_0 (= main@%_4_0 0)))
                  (=> main@.lr.ph6.split_0
                      (= main@%brmerge_0 (or main@%_13_0 main@%_12_0)))
                  (=> main@.lr.ph6.split.split.split_0
                      (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0))
                  (=> (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0)
                      (not main@%brmerge_0))
                  (=> (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0)
                      (= main@%.0.i5_0 0))
                  (=> (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0)
                      (= main@%.01.i3_0 main@%_6_0))
                  (=> (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0)
                      (= main@%.0.i5_1 main@%.0.i5_0))
                  (=> (and main@.lr.ph6.split.split.split_0
                           main@.lr.ph6.split_0)
                      (= main@%.01.i3_1 main@%.01.i3_0))
                  main@.lr.ph6.split.split.split_0)))
    (=> a!2
        (main@.lr.ph6.split.split.split
          main@%.01.i3_1
          main@%.0.i5_1
          main@%loop.bound_0
          main@%_11_0
          main@%_2_0
          main@%_9_0))))))
(assert (forall ((main@.lr.ph6.split.us_0 Bool)
         (main@%_8_0 Bool)
         (main@.lr.ph6_0 Bool)
         (main@%_10_0 Bool)
         (main@%_11_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_9_0 Bool)
         (main@%_5_0 Int)
         (main@%_7_0 Bool)
         (main@entry_0 Bool)
         (main@%_6_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph6_0 (= main@%_10_0 (not (= main@%_1_0 1))))))
  (let ((a!2 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 0))
                  main@%_0_0
                  (= main@%_7_0 (= main@%_6_0 0))
                  (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
                  (=> (and main@.lr.ph6_0 main@entry_0) (not main@%_7_0))
                  (=> main@.lr.ph6_0 (= main@%_8_0 (= main@%_5_0 1)))
                  (=> main@.lr.ph6_0 (= main@%_9_0 (= main@%_2_0 0)))
                  a!1
                  (=> main@.lr.ph6_0 (= main@%_11_0 (ite main@%_10_0 1 0)))
                  (=> main@.lr.ph6.split.us_0
                      (and main@.lr.ph6.split.us_0 main@.lr.ph6_0))
                  (=> (and main@.lr.ph6.split.us_0 main@.lr.ph6_0) main@%_8_0)
                  main@.lr.ph6.split.us_0)))
    (=> a!2 main@.lr.ph6.split.us)))))
(assert (forall ((main@.preheader.split_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.0.i.lcssa_2 Bool)
         (main@%.0.i.lcssa_1 Bool)
         (|tuple(main@entry_0, main@.preheader_0)| Bool)
         (main@%.0.i.lcssa_0 Bool)
         (|tuple(main@.lr.ph6.split_0, main@.preheader_0)| Bool)
         (main@%_7_0 Bool)
         (main@%brmerge_0 Bool)
         (main@entry_0 Bool)
         (main@.lr.ph6.split_0 Bool)
         (main@%_12_0 Bool)
         (main@%_13_0 Bool)
         (main@%_4_0 Int)
         (main@%_3_0 Int)
         (main@%_8_0 Bool)
         (main@.lr.ph6_0 Bool)
         (main@%_10_0 Bool)
         (main@%_11_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_9_0 Bool)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph6_0 (= main@%_10_0 (not (= main@%_1_0 1))))))
  (let ((a!2 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 0))
                  main@%_0_0
                  (= main@%_7_0 (= main@%_6_0 0))
                  (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
                  (=> (and main@.lr.ph6_0 main@entry_0) (not main@%_7_0))
                  (=> main@.lr.ph6_0 (= main@%_8_0 (= main@%_5_0 1)))
                  (=> main@.lr.ph6_0 (= main@%_9_0 (= main@%_2_0 0)))
                  a!1
                  (=> main@.lr.ph6_0 (= main@%_11_0 (ite main@%_10_0 1 0)))
                  (=> main@.lr.ph6.split_0
                      (and main@.lr.ph6.split_0 main@.lr.ph6_0))
                  (=> (and main@.lr.ph6.split_0 main@.lr.ph6_0)
                      (not main@%_8_0))
                  (=> main@.lr.ph6.split_0 (= main@%_12_0 (= main@%_3_0 0)))
                  (=> main@.lr.ph6.split_0 (= main@%_13_0 (= main@%_4_0 0)))
                  (=> main@.lr.ph6.split_0
                      (= main@%brmerge_0 (or main@%_13_0 main@%_12_0)))
                  (=> |tuple(main@.lr.ph6.split_0, main@.preheader_0)|
                      main@.lr.ph6.split_0)
                  (=> |tuple(main@entry_0, main@.preheader_0)| main@entry_0)
                  (=> main@.preheader_0
                      (or |tuple(main@.lr.ph6.split_0, main@.preheader_0)|
                          |tuple(main@entry_0, main@.preheader_0)|))
                  (=> |tuple(main@.lr.ph6.split_0, main@.preheader_0)|
                      main@%brmerge_0)
                  (=> |tuple(main@entry_0, main@.preheader_0)| main@%_7_0)
                  (=> |tuple(main@.lr.ph6.split_0, main@.preheader_0)|
                      (= main@%.0.i.lcssa_0 true))
                  (=> |tuple(main@entry_0, main@.preheader_0)|
                      (= main@%.0.i.lcssa_1 false))
                  (=> |tuple(main@.lr.ph6.split_0, main@.preheader_0)|
                      (= main@%.0.i.lcssa_2 main@%.0.i.lcssa_0))
                  (=> |tuple(main@entry_0, main@.preheader_0)|
                      (= main@%.0.i.lcssa_2 main@%.0.i.lcssa_1))
                  (=> main@.preheader_0 (not main@%.0.i.lcssa_2))
                  (=> main@.preheader.split_0
                      (and main@.preheader.split_0 main@.preheader_0))
                  main@.preheader.split_0)))
    (=> a!2 main@.preheader.split)))))
(assert (forall ((main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%_11_0 Int)
         (main@%loop.bound_0 Int)
         (main@%.0.i5_2 Int)
         (main@%.01.i3_2 Int)
         (main@.lr.ph6.split.split.split_1 Bool)
         (main@%.01.i3_1 Int)
         (main@._crit_edge_0 Bool)
         (main@%.0.i5_1 Int)
         (main@%.34.i_0 Int)
         (main@%.1.i_0 Int)
         (main@%_18_0 Bool)
         (main@%.0.i5_0 Int)
         (main@%_16_0 Bool)
         (main@%_17_0 Int)
         (main@%.12.i.lcssa_1 Int)
         (main@%not..i_0 Bool)
         (main@%.01.i3_0 Int)
         (main@%.12.i.lcssa_0 Int)
         (main@.lr.ph6.split.split.split_0 Bool))
  (let ((a!1 (= main@%_16_0
                (ite (>= main@%.01.i3_0 0)
                     (ite (>= main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          true)
                     (ite (< main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          false))))
        (a!2 (=> main@._crit_edge_0
                 (= main@%_17_0 (ite main@%not..i_0 (- 1) 0)))))
  (let ((a!3 (and (main@.lr.ph6.split.split.split
                    main@%.01.i3_0
                    main@%.0.i5_0
                    main@%loop.bound_0
                    main@%_11_0
                    main@%_2_0
                    main@%_9_0)
                  (=> main@._crit_edge_0
                      (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      main@%_9_0)
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      (= main@%.12.i.lcssa_0 main@%.01.i3_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                  (=> main@._crit_edge_0 a!1)
                  (=> main@._crit_edge_0
                      (= main@%not..i_0 (xor main@%_16_0 true)))
                  a!2
                  (=> main@._crit_edge_0
                      (= main@%.34.i_0 (+ main@%.12.i.lcssa_1 main@%_17_0)))
                  (=> main@._crit_edge_0
                      (= main@%.1.i_0 (ite main@%_16_0 main@%.0.i5_0 1)))
                  (=> main@._crit_edge_0
                      (= main@%_18_0 (= main@%.34.i_0 main@%loop.bound_0)))
                  (=> main@.lr.ph6.split.split.split_1
                      (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0))
                  (=> (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0)
                      (not main@%_18_0))
                  (=> (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0)
                      (= main@%.0.i5_1 main@%.1.i_0))
                  (=> (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0)
                      (= main@%.01.i3_1 main@%.34.i_0))
                  (=> (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0)
                      (= main@%.0.i5_2 main@%.0.i5_1))
                  (=> (and main@.lr.ph6.split.split.split_1 main@._crit_edge_0)
                      (= main@%.01.i3_2 main@%.01.i3_1))
                  main@.lr.ph6.split.split.split_1)))
    (=> a!3
        (main@.lr.ph6.split.split.split
          main@%.01.i3_2
          main@%.0.i5_2
          main@%loop.bound_0
          main@%_11_0
          main@%_2_0
          main@%_9_0))))))
(assert (forall ((main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%.07.i1_1 Int)
         (main@%_11_0 Int)
         (main@%.12.i2_1 Int)
         (main@%loop.bound_0 Int)
         (main@%.0.i5_0 Int)
         (main@%.01.i3_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%.07.i1_0 Int)
         (main@.lr.ph6.split.split.split_0 Bool)
         (main@%.12.i2_0 Int))
  (=> (and (main@.lr.ph6.split.split.split
             main@%.01.i3_0
             main@%.0.i5_0
             main@%loop.bound_0
             main@%_11_0
             main@%_2_0
             main@%_9_0)
           (=> main@.lr.ph_0
               (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0))
           (=> (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0)
               (not main@%_9_0))
           (=> (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0)
               (= main@%.12.i2_0 main@%.01.i3_0))
           (=> (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0)
               (= main@%.07.i1_0 0))
           (=> (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0)
               (= main@%.12.i2_1 main@%.12.i2_0))
           (=> (and main@.lr.ph_0 main@.lr.ph6.split.split.split_0)
               (= main@%.07.i1_1 main@%.07.i1_0))
           main@.lr.ph_0)
      (main@.lr.ph main@%.01.i3_0
                   main@%.0.i5_0
                   main@%loop.bound_0
                   main@%.12.i2_1
                   main@%_11_0
                   main@%.07.i1_1
                   main@%_2_0
                   main@%_9_0))))
(assert (forall ((main@.preheader.split_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.0.i.lcssa_1 Bool)
         (main@%.0.i.lcssa_0 Bool)
         (main@.preheader.loopexit40_0 Bool)
         (main@%phitmp_0 Bool)
         (main@%.1.i_0 Int)
         (main@%_18_0 Bool)
         (main@._crit_edge_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.34.i_0 Int)
         (main@%.0.i5_0 Int)
         (main@%_16_0 Bool)
         (main@%_17_0 Int)
         (main@%.12.i.lcssa_1 Int)
         (main@%not..i_0 Bool)
         (main@%.01.i3_0 Int)
         (main@%.12.i.lcssa_0 Int)
         (main@.lr.ph6.split.split.split_0 Bool)
         (main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%_11_0 Int))
  (let ((a!1 (= main@%_16_0
                (ite (>= main@%.01.i3_0 0)
                     (ite (>= main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          true)
                     (ite (< main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          false))))
        (a!2 (=> main@._crit_edge_0
                 (= main@%_17_0 (ite main@%not..i_0 (- 1) 0)))))
  (let ((a!3 (and (main@.lr.ph6.split.split.split
                    main@%.01.i3_0
                    main@%.0.i5_0
                    main@%loop.bound_0
                    main@%_11_0
                    main@%_2_0
                    main@%_9_0)
                  (=> main@._crit_edge_0
                      (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      main@%_9_0)
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      (= main@%.12.i.lcssa_0 main@%.01.i3_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph6.split.split.split_0)
                      (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                  (=> main@._crit_edge_0 a!1)
                  (=> main@._crit_edge_0
                      (= main@%not..i_0 (xor main@%_16_0 true)))
                  a!2
                  (=> main@._crit_edge_0
                      (= main@%.34.i_0 (+ main@%.12.i.lcssa_1 main@%_17_0)))
                  (=> main@._crit_edge_0
                      (= main@%.1.i_0 (ite main@%_16_0 main@%.0.i5_0 1)))
                  (=> main@._crit_edge_0
                      (= main@%_18_0 (= main@%.34.i_0 main@%loop.bound_0)))
                  (=> main@.preheader.loopexit40_0
                      (and main@.preheader.loopexit40_0 main@._crit_edge_0))
                  (=> (and main@.preheader.loopexit40_0 main@._crit_edge_0)
                      main@%_18_0)
                  (=> main@.preheader.loopexit40_0
                      (= main@%phitmp_0 (= main@%.1.i_0 1)))
                  (=> main@.preheader_0
                      (and main@.preheader_0 main@.preheader.loopexit40_0))
                  (=> (and main@.preheader_0 main@.preheader.loopexit40_0)
                      (= main@%.0.i.lcssa_0 main@%phitmp_0))
                  (=> (and main@.preheader_0 main@.preheader.loopexit40_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@.preheader_0 (not main@%.0.i.lcssa_1))
                  (=> main@.preheader.split_0
                      (and main@.preheader.split_0 main@.preheader_0))
                  main@.preheader.split_0)))
    (=> a!3 main@.preheader.split)))))
(assert (forall ((main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%_11_0 Int)
         (main@%loop.bound_0 Int)
         (main@%.0.i5_2 Int)
         (main@%.01.i3_2 Int)
         (main@.lr.ph6.split.split.split_0 Bool)
         (main@%.01.i3_1 Int)
         (main@._crit_edge_0 Bool)
         (main@%.0.i5_1 Int)
         (main@%.34.i_0 Int)
         (main@%.1.i_0 Int)
         (main@%_18_0 Bool)
         (main@%.0.i5_0 Int)
         (main@%_16_0 Bool)
         (main@%_17_0 Int)
         (main@%.12.i.lcssa_1 Int)
         (main@%not..i_0 Bool)
         (main@%.01.i3_0 Int)
         (main@%.12.i.lcssa_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%spec.select.i_0 Int)
         (main@%_15_0 Bool)
         (main@%_14_0 Int)
         (main@%.07.i1_0 Int)
         (main@%.12.i2_0 Int))
  (let ((a!1 (= main@%_15_0
                (ite (>= main@%_14_0 0)
                     (ite (>= main@%_2_0 0) (< main@%_14_0 main@%_2_0) true)
                     (ite (< main@%_2_0 0) (< main@%_14_0 main@%_2_0) false))))
        (a!2 (= main@%_16_0
                (ite (>= main@%.01.i3_0 0)
                     (ite (>= main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          true)
                     (ite (< main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          false))))
        (a!3 (=> main@._crit_edge_0
                 (= main@%_17_0 (ite main@%not..i_0 (- 1) 0)))))
  (let ((a!4 (and (main@.lr.ph main@%.01.i3_0
                               main@%.0.i5_0
                               main@%loop.bound_0
                               main@%.12.i2_0
                               main@%_11_0
                               main@%.07.i1_0
                               main@%_2_0
                               main@%_9_0)
                  (= main@%spec.select.i_0 (+ main@%.12.i2_0 main@%_11_0))
                  (= main@%_14_0 (+ main@%.07.i1_0 1))
                  a!1
                  (=> main@._crit_edge_0 (and main@._crit_edge_0 main@.lr.ph_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0) (not main@%_15_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0)
                      (= main@%.12.i.lcssa_0 main@%spec.select.i_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0)
                      (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                  (=> main@._crit_edge_0 a!2)
                  (=> main@._crit_edge_0
                      (= main@%not..i_0 (xor main@%_16_0 true)))
                  a!3
                  (=> main@._crit_edge_0
                      (= main@%.34.i_0 (+ main@%.12.i.lcssa_1 main@%_17_0)))
                  (=> main@._crit_edge_0
                      (= main@%.1.i_0 (ite main@%_16_0 main@%.0.i5_0 1)))
                  (=> main@._crit_edge_0
                      (= main@%_18_0 (= main@%.34.i_0 main@%loop.bound_0)))
                  (=> main@.lr.ph6.split.split.split_0
                      (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0))
                  (=> (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0)
                      (not main@%_18_0))
                  (=> (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0)
                      (= main@%.0.i5_1 main@%.1.i_0))
                  (=> (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0)
                      (= main@%.01.i3_1 main@%.34.i_0))
                  (=> (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0)
                      (= main@%.0.i5_2 main@%.0.i5_1))
                  (=> (and main@.lr.ph6.split.split.split_0 main@._crit_edge_0)
                      (= main@%.01.i3_2 main@%.01.i3_1))
                  main@.lr.ph6.split.split.split_0)))
    (=> a!4
        (main@.lr.ph6.split.split.split
          main@%.01.i3_2
          main@%.0.i5_2
          main@%loop.bound_0
          main@%_11_0
          main@%_2_0
          main@%_9_0))))))
(assert (forall ((main@%_9_0 Bool)
         (main@%_2_0 Int)
         (main@%.07.i1_2 Int)
         (main@%_11_0 Int)
         (main@%.12.i2_2 Int)
         (main@%loop.bound_0 Int)
         (main@%.0.i5_0 Int)
         (main@%.01.i3_0 Int)
         (main@.lr.ph_1 Bool)
         (main@%.07.i1_1 Int)
         (main@.lr.ph_0 Bool)
         (main@%.12.i2_1 Int)
         (main@%_14_0 Int)
         (main@%spec.select.i_0 Int)
         (main@%_15_0 Bool)
         (main@%.07.i1_0 Int)
         (main@%.12.i2_0 Int))
  (let ((a!1 (= main@%_15_0
                (ite (>= main@%_14_0 0)
                     (ite (>= main@%_2_0 0) (< main@%_14_0 main@%_2_0) true)
                     (ite (< main@%_2_0 0) (< main@%_14_0 main@%_2_0) false)))))
    (=> (and (main@.lr.ph main@%.01.i3_0
                          main@%.0.i5_0
                          main@%loop.bound_0
                          main@%.12.i2_0
                          main@%_11_0
                          main@%.07.i1_0
                          main@%_2_0
                          main@%_9_0)
             (= main@%spec.select.i_0 (+ main@%.12.i2_0 main@%_11_0))
             (= main@%_14_0 (+ main@%.07.i1_0 1))
             a!1
             (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
             (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_15_0)
             (=> (and main@.lr.ph_1 main@.lr.ph_0)
                 (= main@%.12.i2_1 main@%spec.select.i_0))
             (=> (and main@.lr.ph_1 main@.lr.ph_0)
                 (= main@%.07.i1_1 main@%_14_0))
             (=> (and main@.lr.ph_1 main@.lr.ph_0)
                 (= main@%.12.i2_2 main@%.12.i2_1))
             (=> (and main@.lr.ph_1 main@.lr.ph_0)
                 (= main@%.07.i1_2 main@%.07.i1_1))
             main@.lr.ph_1)
        (main@.lr.ph main@%.01.i3_0
                     main@%.0.i5_0
                     main@%loop.bound_0
                     main@%.12.i2_2
                     main@%_11_0
                     main@%.07.i1_2
                     main@%_2_0
                     main@%_9_0)))))
(assert (forall ((main@.preheader.split_0 Bool)
         (main@.preheader_0 Bool)
         (main@%.0.i.lcssa_1 Bool)
         (main@%.0.i.lcssa_0 Bool)
         (main@.preheader.loopexit40_0 Bool)
         (main@%phitmp_0 Bool)
         (main@%.1.i_0 Int)
         (main@%_18_0 Bool)
         (main@._crit_edge_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.34.i_0 Int)
         (main@%.0.i5_0 Int)
         (main@%_16_0 Bool)
         (main@%_17_0 Int)
         (main@%.12.i.lcssa_1 Int)
         (main@%not..i_0 Bool)
         (main@%.01.i3_0 Int)
         (main@%.12.i.lcssa_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%spec.select.i_0 Int)
         (main@%_15_0 Bool)
         (main@%_2_0 Int)
         (main@%_14_0 Int)
         (main@%.07.i1_0 Int)
         (main@%_11_0 Int)
         (main@%.12.i2_0 Int)
         (main@%_9_0 Bool))
  (let ((a!1 (= main@%_15_0
                (ite (>= main@%_14_0 0)
                     (ite (>= main@%_2_0 0) (< main@%_14_0 main@%_2_0) true)
                     (ite (< main@%_2_0 0) (< main@%_14_0 main@%_2_0) false))))
        (a!2 (= main@%_16_0
                (ite (>= main@%.01.i3_0 0)
                     (ite (>= main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          true)
                     (ite (< main@%.12.i.lcssa_1 0)
                          (< main@%.01.i3_0 main@%.12.i.lcssa_1)
                          false))))
        (a!3 (=> main@._crit_edge_0
                 (= main@%_17_0 (ite main@%not..i_0 (- 1) 0)))))
  (let ((a!4 (and (main@.lr.ph main@%.01.i3_0
                               main@%.0.i5_0
                               main@%loop.bound_0
                               main@%.12.i2_0
                               main@%_11_0
                               main@%.07.i1_0
                               main@%_2_0
                               main@%_9_0)
                  (= main@%spec.select.i_0 (+ main@%.12.i2_0 main@%_11_0))
                  (= main@%_14_0 (+ main@%.07.i1_0 1))
                  a!1
                  (=> main@._crit_edge_0 (and main@._crit_edge_0 main@.lr.ph_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0) (not main@%_15_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0)
                      (= main@%.12.i.lcssa_0 main@%spec.select.i_0))
                  (=> (and main@._crit_edge_0 main@.lr.ph_0)
                      (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                  (=> main@._crit_edge_0 a!2)
                  (=> main@._crit_edge_0
                      (= main@%not..i_0 (xor main@%_16_0 true)))
                  a!3
                  (=> main@._crit_edge_0
                      (= main@%.34.i_0 (+ main@%.12.i.lcssa_1 main@%_17_0)))
                  (=> main@._crit_edge_0
                      (= main@%.1.i_0 (ite main@%_16_0 main@%.0.i5_0 1)))
                  (=> main@._crit_edge_0
                      (= main@%_18_0 (= main@%.34.i_0 main@%loop.bound_0)))
                  (=> main@.preheader.loopexit40_0
                      (and main@.preheader.loopexit40_0 main@._crit_edge_0))
                  (=> (and main@.preheader.loopexit40_0 main@._crit_edge_0)
                      main@%_18_0)
                  (=> main@.preheader.loopexit40_0
                      (= main@%phitmp_0 (= main@%.1.i_0 1)))
                  (=> main@.preheader_0
                      (and main@.preheader_0 main@.preheader.loopexit40_0))
                  (=> (and main@.preheader_0 main@.preheader.loopexit40_0)
                      (= main@%.0.i.lcssa_0 main@%phitmp_0))
                  (=> (and main@.preheader_0 main@.preheader.loopexit40_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@.preheader_0 (not main@%.0.i.lcssa_1))
                  (=> main@.preheader.split_0
                      (and main@.preheader.split_0 main@.preheader_0))
                  main@.preheader.split_0)))
    (=> a!4 main@.preheader.split)))))
(assert (forall ((main@.lr.ph6.split.us_1 Bool) (main@.lr.ph6.split.us_0 Bool))
  (=> (and main@.lr.ph6.split.us
           (=> main@.lr.ph6.split.us_1
               (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0))
           main@.lr.ph6.split.us_1)
      main@.lr.ph6.split.us)))
(assert (=> main@.preheader.split false))
(check-sat)
