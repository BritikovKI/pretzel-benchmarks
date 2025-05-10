(set-logic HORN)
(declare-fun verifier.error (Bool Bool Bool) Bool)
(declare-fun main@entry () Bool)
(declare-fun main@.lr.ph13
             (Int Int Int Int Int Int Int Int Int Int Int Int Int)
             Bool)
(declare-fun main@.lr.ph.split.split (Bool Bool Int Int) Bool)
(declare-fun main@.lr.ph.split.us.split (Bool Bool Int Int) Bool)
(declare-fun main@.lr.ph.split.us.split.us (Bool Bool Int Int) Bool)
(declare-fun main@verifier.error.split () Bool)
(declare-fun main@.lr.ph10 (Int Int Int Int Int Int Int Int Int Int) Bool)
(assert (=> true (verifier.error false false false)))
(assert (=> true (verifier.error false true true)))
(assert (=> true (verifier.error true false true)))
(assert (=> true (verifier.error true true true)))
(assert (=> true main@entry))
(assert (forall ((main@%_10_0 Int)
         (main@%.016.i11_1 Int)
         (main@%_9_0 Int)
         (main@%.014.i12_1 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_8_0 Int)
         (main@.lr.ph13_0 Bool)
         (main@%.016.i11_0 Int)
         (main@entry_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_16_0 Bool)
         (main@%_15_0 Bool)
         (main@%_13_0 Bool)
         (main@%_14_0 Bool)
         (main@%_11_0 Int)
         (main@%_12_0 Int)
         (main@%_0_0 Bool))
  (=> (and main@entry
           (= main@%_0_0 (= main@%loop.bound_0 1))
           main@%_0_0
           (= main@%_13_0 (> main@%_12_0 49))
           (= main@%_14_0 (< main@%_11_0 501))
           (= main@%_15_0 (and main@%_14_0 main@%_13_0))
           main@%_15_0
           (= main@%_16_0 (> main@%_10_0 0))
           (=> main@.lr.ph13_0 (and main@.lr.ph13_0 main@entry_0))
           (=> (and main@.lr.ph13_0 main@entry_0) main@%_16_0)
           (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.014.i12_0 0))
           (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.016.i11_0 0))
           (=> (and main@.lr.ph13_0 main@entry_0)
               (= main@%.014.i12_1 main@%.014.i12_0))
           (=> (and main@.lr.ph13_0 main@entry_0)
               (= main@%.016.i11_1 main@%.016.i11_0))
           main@.lr.ph13_0)
      (main@.lr.ph13 main@%_8_0
                     main@%_7_0
                     main@%_6_0
                     main@%_5_0
                     main@%_4_0
                     main@%_3_0
                     main@%_2_0
                     main@%_1_0
                     main@%loop.bound_0
                     main@%.014.i12_1
                     main@%_9_0
                     main@%.016.i11_1
                     main@%_10_0))))
(assert (forall ((main@%.018.i2_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.split_0 Bool)
         (main@%.018.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_35_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_16_0 Bool)
         (main@entry_0 Bool)
         (main@%_10_0 Int)
         (main@%_15_0 Bool)
         (main@%_13_0 Bool)
         (main@%_14_0 Bool)
         (main@%_11_0 Int)
         (main@%_12_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_13_0 (> main@%_12_0 49))
                  (= main@%_14_0 (< main@%_11_0 501))
                  (= main@%_15_0 (and main@%_14_0 main@%_13_0))
                  main@%_15_0
                  (= main@%_16_0 (> main@%_10_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_16_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.split_0
                      (and main@.lr.ph.split.split_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (not main@%_35_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_0 0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_1 main@%.018.i2_0))
                  main@.lr.ph.split.split_0)))
    (=> a!3
        (main@.lr.ph.split.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2_1))))))
(assert (forall ((main@%.018.i2.us_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split_0 Bool)
         (main@%.018.i2.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_16_0 Bool)
         (main@entry_0 Bool)
         (main@%_10_0 Int)
         (main@%_15_0 Bool)
         (main@%_13_0 Bool)
         (main@%_14_0 Bool)
         (main@%_11_0 Int)
         (main@%_12_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_13_0 (> main@%_12_0 49))
                  (= main@%_14_0 (< main@%_11_0 501))
                  (= main@%_15_0 (and main@%_14_0 main@%_13_0))
                  main@%_15_0
                  (= main@%_16_0 (> main@%_10_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_16_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split_0
                      (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (not main@%or.cond.i_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_0 0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_1 main@%.018.i2.us_0))
                  main@.lr.ph.split.us.split_0)))
    (=> a!3
        (main@.lr.ph.split.us.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2.us_1))))))
(assert (forall ((main@%_8_0 Int)
         (main@%.018.i2.us.us_1 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split.us_0 Bool)
         (main@%.018.i2.us.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_16_0 Bool)
         (main@entry_0 Bool)
         (main@%_10_0 Int)
         (main@%_15_0 Bool)
         (main@%_13_0 Bool)
         (main@%_14_0 Bool)
         (main@%_11_0 Int)
         (main@%_12_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_13_0 (> main@%_12_0 49))
                  (= main@%_14_0 (< main@%_11_0 501))
                  (= main@%_15_0 (and main@%_14_0 main@%_13_0))
                  main@%_15_0
                  (= main@%_16_0 (> main@%_10_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_16_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split.us_0
                      (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      main@%or.cond.i_0)
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_0 0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_1 main@%.018.i2.us.us_0))
                  main@.lr.ph.split.us.split.us_0)))
    (=> a!3
        (main@.lr.ph.split.us.split.us
          main@%_28_0
          main@%_31_0
          main@%.018.i2.us.us_1
          main@%_8_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.preheader_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_25_0 Bool)
         (main@%_8_0 Int)
         (main@%_16_0 Bool)
         (main@entry_0 Bool)
         (main@%_10_0 Int)
         (main@%_15_0 Bool)
         (main@%_13_0 Bool)
         (main@%_14_0 Bool)
         (main@%_11_0 Int)
         (main@%_12_0 Int)
         (main@%_0_0 Bool)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!4 (and main@entry
                  (= main@%_0_0 (= main@%loop.bound_0 1))
                  main@%_0_0
                  (= main@%_13_0 (> main@%_12_0 49))
                  (= main@%_14_0 (< main@%_11_0 501))
                  (= main@%_15_0 (and main@%_14_0 main@%_13_0))
                  main@%_15_0
                  (= main@%_16_0 (> main@%_10_0 0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                  (=> (and main@.preheader_0 main@entry_0) (not main@%_16_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_25_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!1
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!4 main@verifier.error.split)))))
(assert (forall ((main@%_10_0 Int)
         (main@%.016.i11_2 Int)
         (main@%_9_0 Int)
         (main@%.014.i12_2 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_8_0 Int)
         (main@.lr.ph13_1 Bool)
         (main@%.016.i11_1 Int)
         (main@.lr.ph13_0 Bool)
         (main@%.014.i12_1 Int)
         (main@%_18_0 Int)
         (main@%_17_0 Int)
         (main@%_19_0 Bool)
         (main@%.016.i11_0 Int)
         (main@%.014.i12_0 Int))
  (=> (and (main@.lr.ph13 main@%_8_0
                          main@%_7_0
                          main@%_6_0
                          main@%_5_0
                          main@%_4_0
                          main@%_3_0
                          main@%_2_0
                          main@%_1_0
                          main@%loop.bound_0
                          main@%.014.i12_0
                          main@%_9_0
                          main@%.016.i11_0
                          main@%_10_0)
           (= main@%_17_0 (+ main@%.014.i12_0 1))
           (= main@%_18_0 (+ main@%.016.i11_0 1))
           (= main@%_19_0 (< main@%_18_0 main@%_10_0))
           (=> main@.lr.ph13_1 (and main@.lr.ph13_1 main@.lr.ph13_0))
           (=> (and main@.lr.ph13_1 main@.lr.ph13_0) main@%_19_0)
           (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
               (= main@%.014.i12_1 main@%_17_0))
           (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
               (= main@%.016.i11_1 main@%_18_0))
           (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
               (= main@%.014.i12_2 main@%.014.i12_1))
           (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
               (= main@%.016.i11_2 main@%.016.i11_1))
           main@.lr.ph13_1)
      (main@.lr.ph13 main@%_8_0
                     main@%_7_0
                     main@%_6_0
                     main@%_5_0
                     main@%_4_0
                     main@%_3_0
                     main@%_2_0
                     main@%_1_0
                     main@%loop.bound_0
                     main@%.014.i12_2
                     main@%_9_0
                     main@%.016.i11_2
                     main@%_10_0))))
(assert (forall ((main@%loop.bound_0 Int)
         (main@%.115.i9_1 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_8_0 Int)
         (main@.lr.ph10_0 Bool)
         (main@%.115.i9_0 Int)
         (main@_23_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_24_0 Bool)
         (main@%_21_0 Bool)
         (|tuple(main@.lr.ph10.peel_0, main@_23_0)| Bool)
         (main@_22_0 Bool)
         (main@.lr.ph10.peel_0 Bool)
         (main@%_9_0 Int)
         (main@%_20_0 Bool)
         (main@%_19_0 Bool)
         (main@.lr.ph13_0 Bool)
         (main@%_10_0 Int)
         (main@%_18_0 Int)
         (main@%.016.i11_0 Int)
         (main@%_17_0 Int))
  (let ((a!1 (=> main@.lr.ph10.peel_0
                 (= main@%_20_0 (ite (>= main@%_9_0 0) (< main@%_9_0 2) false)))))
  (let ((a!2 (and (main@.lr.ph13 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%loop.bound_0
                                 main@%.014.i12_0
                                 main@%_9_0
                                 main@%.016.i11_0
                                 main@%_10_0)
                  (= main@%_17_0 (+ main@%.014.i12_0 1))
                  (= main@%_18_0 (+ main@%.016.i11_0 1))
                  (= main@%_19_0 (< main@%_18_0 main@%_10_0))
                  (=> main@.lr.ph10.peel_0
                      (and main@.lr.ph10.peel_0 main@.lr.ph13_0))
                  (=> (and main@.lr.ph10.peel_0 main@.lr.ph13_0)
                      (not main@%_19_0))
                  a!1
                  (=> main@.lr.ph10.peel_0 main@%_20_0)
                  (=> main@.lr.ph10.peel_0 (= main@%_21_0 (= main@%_9_0 1)))
                  (=> main@_22_0 (and main@_22_0 main@.lr.ph10.peel_0))
                  (=> (and main@_22_0 main@.lr.ph10.peel_0) (not main@%_21_0))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)|
                      main@.lr.ph10.peel_0)
                  (=> main@_23_0
                      (or (and main@_23_0 main@_22_0)
                          |tuple(main@.lr.ph10.peel_0, main@_23_0)|))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)| main@%_21_0)
                  (=> main@_23_0 (= main@%_24_0 (= main@%.014.i12_0 0)))
                  (=> main@.lr.ph10_0 (and main@.lr.ph10_0 main@_23_0))
                  (=> (and main@.lr.ph10_0 main@_23_0) (not main@%_24_0))
                  (=> (and main@.lr.ph10_0 main@_23_0)
                      (= main@%.115.i9_0 main@%.014.i12_0))
                  (=> (and main@.lr.ph10_0 main@_23_0)
                      (= main@%.115.i9_1 main@%.115.i9_0))
                  main@.lr.ph10_0)))
    (=> a!2
        (main@.lr.ph10 main@%_8_0
                       main@%_7_0
                       main@%_6_0
                       main@%_5_0
                       main@%_4_0
                       main@%_3_0
                       main@%_2_0
                       main@%_1_0
                       main@%.115.i9_1
                       main@%loop.bound_0))))))
(assert (forall ((main@%.018.i2_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.split_0 Bool)
         (main@%.018.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_35_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_24_0 Bool)
         (main@_23_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_21_0 Bool)
         (|tuple(main@.lr.ph10.peel_0, main@_23_0)| Bool)
         (main@_22_0 Bool)
         (main@.lr.ph10.peel_0 Bool)
         (main@%_9_0 Int)
         (main@%_20_0 Bool)
         (main@%_19_0 Bool)
         (main@.lr.ph13_0 Bool)
         (main@%_10_0 Int)
         (main@%_18_0 Int)
         (main@%.016.i11_0 Int)
         (main@%_17_0 Int)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph10.peel_0
                 (= main@%_20_0 (ite (>= main@%_9_0 0) (< main@%_9_0 2) false))))
        (a!2 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!3 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!4 (and (main@.lr.ph13 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%loop.bound_0
                                 main@%.014.i12_0
                                 main@%_9_0
                                 main@%.016.i11_0
                                 main@%_10_0)
                  (= main@%_17_0 (+ main@%.014.i12_0 1))
                  (= main@%_18_0 (+ main@%.016.i11_0 1))
                  (= main@%_19_0 (< main@%_18_0 main@%_10_0))
                  (=> main@.lr.ph10.peel_0
                      (and main@.lr.ph10.peel_0 main@.lr.ph13_0))
                  (=> (and main@.lr.ph10.peel_0 main@.lr.ph13_0)
                      (not main@%_19_0))
                  a!1
                  (=> main@.lr.ph10.peel_0 main@%_20_0)
                  (=> main@.lr.ph10.peel_0 (= main@%_21_0 (= main@%_9_0 1)))
                  (=> main@_22_0 (and main@_22_0 main@.lr.ph10.peel_0))
                  (=> (and main@_22_0 main@.lr.ph10.peel_0) (not main@%_21_0))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)|
                      main@.lr.ph10.peel_0)
                  (=> main@_23_0
                      (or (and main@_23_0 main@_22_0)
                          |tuple(main@.lr.ph10.peel_0, main@_23_0)|))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)| main@%_21_0)
                  (=> main@_23_0 (= main@%_24_0 (= main@%.014.i12_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_23_0))
                  (=> (and main@.preheader_0 main@_23_0) main@%_24_0)
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!2
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!3
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.split_0
                      (and main@.lr.ph.split.split_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (not main@%_35_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_0 0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_1 main@%.018.i2_0))
                  main@.lr.ph.split.split_0)))
    (=> a!4
        (main@.lr.ph.split.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2_1))))))
(assert (forall ((main@%.018.i2.us_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split_0 Bool)
         (main@%.018.i2.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_24_0 Bool)
         (main@_23_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_21_0 Bool)
         (|tuple(main@.lr.ph10.peel_0, main@_23_0)| Bool)
         (main@_22_0 Bool)
         (main@.lr.ph10.peel_0 Bool)
         (main@%_9_0 Int)
         (main@%_20_0 Bool)
         (main@%_19_0 Bool)
         (main@.lr.ph13_0 Bool)
         (main@%_10_0 Int)
         (main@%_18_0 Int)
         (main@%.016.i11_0 Int)
         (main@%_17_0 Int)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph10.peel_0
                 (= main@%_20_0 (ite (>= main@%_9_0 0) (< main@%_9_0 2) false))))
        (a!2 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!3 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!4 (and (main@.lr.ph13 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%loop.bound_0
                                 main@%.014.i12_0
                                 main@%_9_0
                                 main@%.016.i11_0
                                 main@%_10_0)
                  (= main@%_17_0 (+ main@%.014.i12_0 1))
                  (= main@%_18_0 (+ main@%.016.i11_0 1))
                  (= main@%_19_0 (< main@%_18_0 main@%_10_0))
                  (=> main@.lr.ph10.peel_0
                      (and main@.lr.ph10.peel_0 main@.lr.ph13_0))
                  (=> (and main@.lr.ph10.peel_0 main@.lr.ph13_0)
                      (not main@%_19_0))
                  a!1
                  (=> main@.lr.ph10.peel_0 main@%_20_0)
                  (=> main@.lr.ph10.peel_0 (= main@%_21_0 (= main@%_9_0 1)))
                  (=> main@_22_0 (and main@_22_0 main@.lr.ph10.peel_0))
                  (=> (and main@_22_0 main@.lr.ph10.peel_0) (not main@%_21_0))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)|
                      main@.lr.ph10.peel_0)
                  (=> main@_23_0
                      (or (and main@_23_0 main@_22_0)
                          |tuple(main@.lr.ph10.peel_0, main@_23_0)|))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)| main@%_21_0)
                  (=> main@_23_0 (= main@%_24_0 (= main@%.014.i12_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_23_0))
                  (=> (and main@.preheader_0 main@_23_0) main@%_24_0)
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!2
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!3
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split_0
                      (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (not main@%or.cond.i_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_0 0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_1 main@%.018.i2.us_0))
                  main@.lr.ph.split.us.split_0)))
    (=> a!4
        (main@.lr.ph.split.us.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2.us_1))))))
(assert (forall ((main@%_8_0 Int)
         (main@%.018.i2.us.us_1 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split.us_0 Bool)
         (main@%.018.i2.us.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_24_0 Bool)
         (main@_23_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_21_0 Bool)
         (|tuple(main@.lr.ph10.peel_0, main@_23_0)| Bool)
         (main@_22_0 Bool)
         (main@.lr.ph10.peel_0 Bool)
         (main@%_9_0 Int)
         (main@%_20_0 Bool)
         (main@%_19_0 Bool)
         (main@.lr.ph13_0 Bool)
         (main@%_10_0 Int)
         (main@%_18_0 Int)
         (main@%.016.i11_0 Int)
         (main@%_17_0 Int)
         (main@%loop.bound_0 Int))
  (let ((a!1 (=> main@.lr.ph10.peel_0
                 (= main@%_20_0 (ite (>= main@%_9_0 0) (< main@%_9_0 2) false))))
        (a!2 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!3 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!4 (and (main@.lr.ph13 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%loop.bound_0
                                 main@%.014.i12_0
                                 main@%_9_0
                                 main@%.016.i11_0
                                 main@%_10_0)
                  (= main@%_17_0 (+ main@%.014.i12_0 1))
                  (= main@%_18_0 (+ main@%.016.i11_0 1))
                  (= main@%_19_0 (< main@%_18_0 main@%_10_0))
                  (=> main@.lr.ph10.peel_0
                      (and main@.lr.ph10.peel_0 main@.lr.ph13_0))
                  (=> (and main@.lr.ph10.peel_0 main@.lr.ph13_0)
                      (not main@%_19_0))
                  a!1
                  (=> main@.lr.ph10.peel_0 main@%_20_0)
                  (=> main@.lr.ph10.peel_0 (= main@%_21_0 (= main@%_9_0 1)))
                  (=> main@_22_0 (and main@_22_0 main@.lr.ph10.peel_0))
                  (=> (and main@_22_0 main@.lr.ph10.peel_0) (not main@%_21_0))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)|
                      main@.lr.ph10.peel_0)
                  (=> main@_23_0
                      (or (and main@_23_0 main@_22_0)
                          |tuple(main@.lr.ph10.peel_0, main@_23_0)|))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)| main@%_21_0)
                  (=> main@_23_0 (= main@%_24_0 (= main@%.014.i12_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_23_0))
                  (=> (and main@.preheader_0 main@_23_0) main@%_24_0)
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!2
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!3
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split.us_0
                      (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      main@%or.cond.i_0)
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_0 0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_1 main@%.018.i2.us.us_0))
                  main@.lr.ph.split.us.split.us_0)))
    (=> a!4
        (main@.lr.ph.split.us.split.us
          main@%_28_0
          main@%_31_0
          main@%.018.i2.us.us_1
          main@%_8_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.preheader_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_25_0 Bool)
         (main@%_8_0 Int)
         (main@%_24_0 Bool)
         (main@_23_0 Bool)
         (main@%.014.i12_0 Int)
         (main@%_21_0 Bool)
         (|tuple(main@.lr.ph10.peel_0, main@_23_0)| Bool)
         (main@_22_0 Bool)
         (main@.lr.ph10.peel_0 Bool)
         (main@%_9_0 Int)
         (main@%_20_0 Bool)
         (main@%_19_0 Bool)
         (main@.lr.ph13_0 Bool)
         (main@%_10_0 Int)
         (main@%_18_0 Int)
         (main@%.016.i11_0 Int)
         (main@%_17_0 Int)
         (main@%loop.bound_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int))
  (let ((a!1 (=> main@.lr.ph10.peel_0
                 (= main@%_20_0 (ite (>= main@%_9_0 0) (< main@%_9_0 2) false))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!4 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!5 (and (main@.lr.ph13 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%loop.bound_0
                                 main@%.014.i12_0
                                 main@%_9_0
                                 main@%.016.i11_0
                                 main@%_10_0)
                  (= main@%_17_0 (+ main@%.014.i12_0 1))
                  (= main@%_18_0 (+ main@%.016.i11_0 1))
                  (= main@%_19_0 (< main@%_18_0 main@%_10_0))
                  (=> main@.lr.ph10.peel_0
                      (and main@.lr.ph10.peel_0 main@.lr.ph13_0))
                  (=> (and main@.lr.ph10.peel_0 main@.lr.ph13_0)
                      (not main@%_19_0))
                  a!1
                  (=> main@.lr.ph10.peel_0 main@%_20_0)
                  (=> main@.lr.ph10.peel_0 (= main@%_21_0 (= main@%_9_0 1)))
                  (=> main@_22_0 (and main@_22_0 main@.lr.ph10.peel_0))
                  (=> (and main@_22_0 main@.lr.ph10.peel_0) (not main@%_21_0))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)|
                      main@.lr.ph10.peel_0)
                  (=> main@_23_0
                      (or (and main@_23_0 main@_22_0)
                          |tuple(main@.lr.ph10.peel_0, main@_23_0)|))
                  (=> |tuple(main@.lr.ph10.peel_0, main@_23_0)| main@%_21_0)
                  (=> main@_23_0 (= main@%_24_0 (= main@%.014.i12_0 0)))
                  (=> main@.preheader_0 (and main@.preheader_0 main@_23_0))
                  (=> (and main@.preheader_0 main@_23_0) main@%_24_0)
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_25_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!4
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!5 main@verifier.error.split)))))
(assert (forall ((main@%loop.bound_0 Int)
         (main@%.115.i9_2 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_8_0 Int)
         (main@.lr.ph10_1 Bool)
         (main@%.115.i9_1 Int)
         (main@.lr.ph10_0 Bool)
         (main@%.7.i_0 Int)
         (main@%_40_0 Bool)
         (main@%.115.i9_0 Int))
  (let ((a!1 (and (main@.lr.ph10 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%.115.i9_0
                                 main@%loop.bound_0)
                  (= main@%.7.i_0 (+ main@%.115.i9_0 (- 1)))
                  (= main@%_40_0 (> main@%.115.i9_0 main@%loop.bound_0))
                  (=> main@.lr.ph10_1 (and main@.lr.ph10_1 main@.lr.ph10_0))
                  (=> (and main@.lr.ph10_1 main@.lr.ph10_0) main@%_40_0)
                  (=> (and main@.lr.ph10_1 main@.lr.ph10_0)
                      (= main@%.115.i9_1 main@%.7.i_0))
                  (=> (and main@.lr.ph10_1 main@.lr.ph10_0)
                      (= main@%.115.i9_2 main@%.115.i9_1))
                  main@.lr.ph10_1)))
    (=> a!1
        (main@.lr.ph10 main@%_8_0
                       main@%_7_0
                       main@%_6_0
                       main@%_5_0
                       main@%_4_0
                       main@%_3_0
                       main@%_2_0
                       main@%_1_0
                       main@%.115.i9_2
                       main@%loop.bound_0)))))
(assert (forall ((main@%.018.i2_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.split_0 Bool)
         (main@%.018.i2_0 Int)
         (main@.lr.ph_0 Bool)
         (main@%_35_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_40_0 Bool)
         (main@.lr.ph10_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.115.i9_0 Int)
         (main@%.7.i_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and (main@.lr.ph10 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%.115.i9_0
                                 main@%loop.bound_0)
                  (= main@%.7.i_0 (+ main@%.115.i9_0 (- 1)))
                  (= main@%_40_0 (> main@%.115.i9_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph10_0))
                  (=> (and main@.preheader_0 main@.lr.ph10_0) (not main@%_40_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.split_0
                      (and main@.lr.ph.split.split_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (not main@%_35_0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_0 0))
                  (=> (and main@.lr.ph.split.split_0 main@.lr.ph_0)
                      (= main@%.018.i2_1 main@%.018.i2_0))
                  main@.lr.ph.split.split_0)))
    (=> a!3
        (main@.lr.ph.split.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2_1))))))
(assert (forall ((main@%.018.i2.us_1 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split_0 Bool)
         (main@%.018.i2.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_40_0 Bool)
         (main@.lr.ph10_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.115.i9_0 Int)
         (main@%.7.i_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and (main@.lr.ph10 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%.115.i9_0
                                 main@%loop.bound_0)
                  (= main@%.7.i_0 (+ main@%.115.i9_0 (- 1)))
                  (= main@%_40_0 (> main@%.115.i9_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph10_0))
                  (=> (and main@.preheader_0 main@.lr.ph10_0) (not main@%_40_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split_0
                      (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (not main@%or.cond.i_0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_0 0))
                  (=> (and main@.lr.ph.split.us.split_0 main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us_1 main@%.018.i2.us_0))
                  main@.lr.ph.split.us.split_0)))
    (=> a!3
        (main@.lr.ph.split.us.split
          main@%_28_0
          main@%_31_0
          main@%_8_0
          main@%.018.i2.us_1))))))
(assert (forall ((main@%_8_0 Int)
         (main@%.018.i2.us.us_1 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split.us_0 Bool)
         (main@%.018.i2.us.us_0 Int)
         (main@.lr.ph.split.us_0 Bool)
         (main@%or.cond.i_0 Bool)
         (main@%_35_0 Bool)
         (main@.lr.ph_0 Bool)
         (main@%_34_0 Bool)
         (main@%_1_0 Int)
         (main@%_32_0 Bool)
         (main@%_33_0 Bool)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_29_0 Bool)
         (main@%_30_0 Bool)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_26_0 Bool)
         (main@%_27_0 Bool)
         (main@%_6_0 Int)
         (main@%_7_0 Int)
         (main@%_25_0 Bool)
         (main@.preheader_0 Bool)
         (main@%_40_0 Bool)
         (main@.lr.ph10_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.115.i9_0 Int)
         (main@%.7.i_0 Int))
  (let ((a!1 (=> main@.lr.ph_0 (= main@%_26_0 (> main@%_7_0 (- 1)))))
        (a!2 (=> main@.lr.ph_0 (= main@%_29_0 (> main@%_5_0 (- 1))))))
  (let ((a!3 (and (main@.lr.ph10 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%.115.i9_0
                                 main@%loop.bound_0)
                  (= main@%.7.i_0 (+ main@%.115.i9_0 (- 1)))
                  (= main@%_40_0 (> main@%.115.i9_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph10_0))
                  (=> (and main@.preheader_0 main@.lr.ph10_0) (not main@%_40_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                  (=> (and main@.lr.ph_0 main@.preheader_0) main@%_25_0)
                  a!1
                  (=> main@.lr.ph_0 (= main@%_27_0 (< main@%_6_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_28_0 (and main@%_27_0 main@%_26_0)))
                  a!2
                  (=> main@.lr.ph_0 (= main@%_30_0 (< main@%_4_0 2)))
                  (=> main@.lr.ph_0
                      (= main@%_31_0 (and main@%_30_0 main@%_29_0)))
                  (=> main@.lr.ph_0 (= main@%_32_0 (= main@%_3_0 1)))
                  (=> main@.lr.ph_0 (= main@%_33_0 (= main@%_2_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%or.cond.i_0 (and main@%_33_0 main@%_32_0)))
                  (=> main@.lr.ph_0 (= main@%_34_0 (= main@%_1_0 1)))
                  (=> main@.lr.ph_0
                      (= main@%_35_0 (or main@%_34_0 main@%or.cond.i_0)))
                  (=> main@.lr.ph.split.us_0
                      (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                  (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_35_0)
                  (=> main@.lr.ph.split.us.split.us_0
                      (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      main@%or.cond.i_0)
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_0 0))
                  (=> (and main@.lr.ph.split.us.split.us_0
                           main@.lr.ph.split.us_0)
                      (= main@%.018.i2.us.us_1 main@%.018.i2.us.us_0))
                  main@.lr.ph.split.us.split.us_0)))
    (=> a!3
        (main@.lr.ph.split.us.split.us
          main@%_28_0
          main@%_31_0
          main@%.018.i2.us.us_1
          main@%_8_0))))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.preheader_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_25_0 Bool)
         (main@%_8_0 Int)
         (main@%_40_0 Bool)
         (main@.lr.ph10_0 Bool)
         (main@%loop.bound_0 Int)
         (main@%.115.i9_0 Int)
         (main@%.7.i_0 Int)
         (main@%_1_0 Int)
         (main@%_2_0 Int)
         (main@%_3_0 Int)
         (main@%_4_0 Int)
         (main@%_5_0 Int)
         (main@%_6_0 Int)
         (main@%_7_0 Int))
  (let ((a!1 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!4 (and (main@.lr.ph10 main@%_8_0
                                 main@%_7_0
                                 main@%_6_0
                                 main@%_5_0
                                 main@%_4_0
                                 main@%_3_0
                                 main@%_2_0
                                 main@%_1_0
                                 main@%.115.i9_0
                                 main@%loop.bound_0)
                  (= main@%.7.i_0 (+ main@%.115.i9_0 (- 1)))
                  (= main@%_40_0 (> main@%.115.i9_0 main@%loop.bound_0))
                  (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph10_0))
                  (=> (and main@.preheader_0 main@.lr.ph10_0) (not main@%_40_0))
                  (=> main@.preheader_0 (= main@%_25_0 (> main@%_8_0 0)))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.preheader_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (not main@%_25_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.preheader_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!1
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!4 main@verifier.error.split)))))
(assert (forall ((main@%.018.i2_2 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.split_1 Bool)
         (main@%.018.i2_1 Int)
         (main@.lr.ph.split.split_0 Bool)
         (main@%_41_0 Int)
         (main@%_42_0 Bool)
         (main@%.018.i2_0 Int))
  (=> (and (main@.lr.ph.split.split
             main@%_28_0
             main@%_31_0
             main@%_8_0
             main@%.018.i2_0)
           main@%_28_0
           main@%_31_0
           (= main@%_41_0 (+ main@%.018.i2_0 1))
           (= main@%_42_0 (< main@%_41_0 main@%_8_0))
           (=> main@.lr.ph.split.split_1
               (and main@.lr.ph.split.split_1 main@.lr.ph.split.split_0))
           (=> (and main@.lr.ph.split.split_1 main@.lr.ph.split.split_0)
               main@%_42_0)
           (=> (and main@.lr.ph.split.split_1 main@.lr.ph.split.split_0)
               (= main@%.018.i2_1 main@%_41_0))
           (=> (and main@.lr.ph.split.split_1 main@.lr.ph.split.split_0)
               (= main@%.018.i2_2 main@%.018.i2_1))
           main@.lr.ph.split.split_1)
      (main@.lr.ph.split.split
        main@%_28_0
        main@%_31_0
        main@%_8_0
        main@%.018.i2_2))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.lr.ph.split.split_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_42_0 Bool)
         (main@%_8_0 Int)
         (main@%_41_0 Int)
         (main@%.018.i2_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool))
  (let ((a!1 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!4 (and (main@.lr.ph.split.split
                    main@%_28_0
                    main@%_31_0
                    main@%_8_0
                    main@%.018.i2_0)
                  main@%_28_0
                  main@%_31_0
                  (= main@%_41_0 (+ main@%.018.i2_0 1))
                  (= main@%_42_0 (< main@%_41_0 main@%_8_0))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.lr.ph.split.split_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (not main@%_42_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.012.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.010.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.0.i.lcssa_0 1))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.split_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!1
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!4 main@verifier.error.split)))))
(assert (forall ((main@%.018.i2.us_2 Int)
         (main@%_8_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split_1 Bool)
         (main@%.018.i2.us_1 Int)
         (main@.lr.ph.split.us.split_0 Bool)
         (main@%_38_0 Int)
         (main@%_39_0 Bool)
         (main@%.018.i2.us_0 Int))
  (=> (and (main@.lr.ph.split.us.split
             main@%_28_0
             main@%_31_0
             main@%_8_0
             main@%.018.i2.us_0)
           main@%_28_0
           main@%_31_0
           (= main@%_38_0 (+ main@%.018.i2.us_0 1))
           (= main@%_39_0 (< main@%_38_0 main@%_8_0))
           (=> main@.lr.ph.split.us.split_1
               (and main@.lr.ph.split.us.split_1 main@.lr.ph.split.us.split_0))
           (=> (and main@.lr.ph.split.us.split_1 main@.lr.ph.split.us.split_0)
               main@%_39_0)
           (=> (and main@.lr.ph.split.us.split_1 main@.lr.ph.split.us.split_0)
               (= main@%.018.i2.us_1 main@%_38_0))
           (=> (and main@.lr.ph.split.us.split_1 main@.lr.ph.split.us.split_0)
               (= main@%.018.i2.us_2 main@%.018.i2.us_1))
           main@.lr.ph.split.us.split_1)
      (main@.lr.ph.split.us.split
        main@%_28_0
        main@%_31_0
        main@%_8_0
        main@%.018.i2.us_2))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.lr.ph.split.us.split_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_39_0 Bool)
         (main@%_8_0 Int)
         (main@%_38_0 Int)
         (main@%.018.i2.us_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool))
  (let ((a!1 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!4 (and (main@.lr.ph.split.us.split
                    main@%_28_0
                    main@%_31_0
                    main@%_8_0
                    main@%.018.i2.us_0)
                  main@%_28_0
                  main@%_31_0
                  (= main@%_38_0 (+ main@%.018.i2.us_0 1))
                  (= main@%_39_0 (< main@%_38_0 main@%_8_0))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0 main@.lr.ph.split.us.split_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (not main@%_39_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.012.i.lcssa_0 1))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.010.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.0.i.lcssa_0 0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0 main@.lr.ph.split.us.split_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!1
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!4 main@verifier.error.split)))))
(assert (forall ((main@%_8_0 Int)
         (main@%.018.i2.us.us_2 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool)
         (main@.lr.ph.split.us.split.us_1 Bool)
         (main@%.018.i2.us.us_1 Int)
         (main@.lr.ph.split.us.split.us_0 Bool)
         (main@%_36_0 Int)
         (main@%_37_0 Bool)
         (main@%.018.i2.us.us_0 Int))
  (=> (and (main@.lr.ph.split.us.split.us
             main@%_28_0
             main@%_31_0
             main@%.018.i2.us.us_0
             main@%_8_0)
           main@%_28_0
           main@%_31_0
           (= main@%_36_0 (+ main@%.018.i2.us.us_0 1))
           (= main@%_37_0 (< main@%_36_0 main@%_8_0))
           (=> main@.lr.ph.split.us.split.us_1
               (and main@.lr.ph.split.us.split.us_1
                    main@.lr.ph.split.us.split.us_0))
           (=> (and main@.lr.ph.split.us.split.us_1
                    main@.lr.ph.split.us.split.us_0)
               main@%_37_0)
           (=> (and main@.lr.ph.split.us.split.us_1
                    main@.lr.ph.split.us.split.us_0)
               (= main@%.018.i2.us.us_1 main@%_36_0))
           (=> (and main@.lr.ph.split.us.split.us_1
                    main@.lr.ph.split.us.split.us_0)
               (= main@%.018.i2.us.us_2 main@%.018.i2.us.us_1))
           main@.lr.ph.split.us.split.us_1)
      (main@.lr.ph.split.us.split.us
        main@%_28_0
        main@%_31_0
        main@%.018.i2.us.us_2
        main@%_8_0))))
(assert (forall ((main@verifier.error.split_0 Bool)
         (main@verifier.error_0 Bool)
         (main@%or.cond9.i_0 Bool)
         (main@%or.cond7.i_0 Bool)
         (main@%_48_0 Bool)
         (main@%.010.i.lcssa_1 Int)
         (main@%_46_0 Bool)
         (main@%_47_0 Bool)
         (main@%.012.i.lcssa_1 Int)
         (main@%.0.i.lcssa_1 Int)
         (main@%or.cond5.i_0 Bool)
         (main@%_45_0 Bool)
         (main@%or.cond3.i_0 Bool)
         (main@%_43_0 Bool)
         (main@%_44_0 Bool)
         (main@%.0.i.lcssa_0 Int)
         (main@.lr.ph.split.us.split.us_0 Bool)
         (main@%.010.i.lcssa_0 Int)
         (main@%.012.i.lcssa_0 Int)
         (main@%_37_0 Bool)
         (main@%_8_0 Int)
         (main@%_36_0 Int)
         (main@%.018.i2.us.us_0 Int)
         (main@%_31_0 Bool)
         (main@%_28_0 Bool))
  (let ((a!1 (=> main@verifier.error_0
                 (= main@%_45_0 (not (= main@%.0.i.lcssa_1 1)))))
        (a!2 (=> main@verifier.error_0
                 (= main@%_47_0 (not (= main@%.012.i.lcssa_1 1)))))
        (a!3 (=> main@verifier.error_0
                 (= main@%_48_0 (not (= main@%.010.i.lcssa_1 1))))))
  (let ((a!4 (and (main@.lr.ph.split.us.split.us
                    main@%_28_0
                    main@%_31_0
                    main@%.018.i2.us.us_0
                    main@%_8_0)
                  main@%_28_0
                  main@%_31_0
                  (= main@%_36_0 (+ main@%.018.i2.us.us_0 1))
                  (= main@%_37_0 (< main@%_36_0 main@%_8_0))
                  (=> main@verifier.error_0
                      (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (not main@%_37_0))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.012.i.lcssa_0 1))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.010.i.lcssa_0 1))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.0.i.lcssa_0 0))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.012.i.lcssa_1 main@%.012.i.lcssa_0))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                  (=> (and main@verifier.error_0
                           main@.lr.ph.split.us.split.us_0)
                      (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                  (=> main@verifier.error_0
                      (= main@%_43_0 (= main@%.010.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%_44_0 (= main@%.012.i.lcssa_1 1)))
                  (=> main@verifier.error_0
                      (= main@%or.cond3.i_0 (or main@%_44_0 main@%_43_0)))
                  a!1
                  (=> main@verifier.error_0
                      (= main@%or.cond5.i_0
                         (and main@%or.cond3.i_0 main@%_45_0)))
                  (=> main@verifier.error_0 (not main@%or.cond5.i_0))
                  (=> main@verifier.error_0
                      (= main@%_46_0 (= main@%.0.i.lcssa_1 1)))
                  a!2
                  (=> main@verifier.error_0
                      (= main@%or.cond7.i_0 (and main@%_47_0 main@%_46_0)))
                  a!3
                  (=> main@verifier.error_0
                      (= main@%or.cond9.i_0
                         (and main@%_48_0 main@%or.cond7.i_0)))
                  (=> main@verifier.error_0 (not main@%or.cond9.i_0))
                  (=> main@verifier.error.split_0
                      (and main@verifier.error.split_0 main@verifier.error_0))
                  main@verifier.error.split_0)))
    (=> a!4 main@verifier.error.split)))))
(assert (=> main@verifier.error.split false))
(check-sat)
